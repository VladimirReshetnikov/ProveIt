import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.FiniteHeads.GaussianLogGammaEulerHead
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.EndpointRates.GaussianNamedDifferenceQuotientProperness

/-!
# Unit shift of the weighted Euler logarithm

Use the canonical signed Gaussian encoding to add exactly one and cancel
the shared `z log(N)` term in the two original product names.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerProductShift

open_ipra
open ComplexLogarithmRemainder (code scale oneCode eval_re_code eval_im_code)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerHead (argument productF productData)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast right_distributive multiply_one_left)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (qadd canonical_unique ofGaussian_canonical ofGaussian_represents
  qadd_represents qadd_canonical represents_congr)
open GaussianRationalReciprocal (qone_represents_scaled)
open GaussianRationalSyntheticDivision (qone)
open GaussianRootAlgebra (equal_of_values re_add im_add re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data

theorem argument_shift (A B D neg : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qadd qone (argument A B D neg) ≐ argument (A+D) B D neg := by
  let im : ZT n := ⟨RationalArithmetic.select neg B zero, RationalArithmetic.select neg zero B⟩
  let z := code (ZT.ofNat A) im
  let w := code (ZT.ofNat (A+D)) im
  have rep := qadd_represents qone (argument A B D neg) (scale D oneCode) z D hD
    (qone_represents_scaled D) (ofGaussian_represents z D hD)
  apply canonical_unique _ _ w D (qadd_canonical _ _) (ofGaussian_canonical w D hD) hD
    (hrv := ofGaussian_represents w D hD)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) rep
  apply equal_of_values
  · simp only [z,w,re_add,re_scale,re_one,eval_re_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  · simp only [z,w,im_add,im_scale,im_one,eval_im_code]
    ring

theorem difference (A B D neg N : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (F productF productF) logF
      (X (productData (A+D) B D neg N) (productData A B D neg N)) (L N one) := by
  let z := argument A B D neg
  let w := argument (A+D) B D neg
  let x := L N one
  let M := multiplyF (addF constantF constantF) logF
  let m := multiplyData (addF constantF constantF) logF (addData qone z) x
  let a := multiplyData constantF logF qone x
  let b := productData A B D neg N
  let c := productData (A+D) B D neg N
  have hx := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  have ha := multiply_fast constantF logF qone x (constant_regular _) hx
  have hb := multiply_fast constantF logF z x (constant_regular _) hx
  have hc := multiply_fast constantF logF w x (constant_regular _) hx
  have add := GaussianNamedGammaHalfShift.constant_sum qone z w (argument_shift A B D neg hD)
  have first : Γ ⊢[PRAAx] crossEquivalent productF M c m :=
    multiply_cross constantF (addF constantF constantF) logF logF w (addData qone z) x x
      (constant_regular _) (add_fast _ _ _ _ (constant_regular _) (constant_regular _)) hx hx
      (cross_symm _ _ _ _ add) (cross_refl _ _ hx)
  have expanded : Γ ⊢[PRAAx] crossEquivalent productF (addF productF productF) c (addData a b) :=
    cross_trans productF M (addF productF productF) c m (addData a b) first
      (right_distributive constantF constantF logF qone z x (constant_regular _) (constant_regular _) hx)
  have cancel := difference_proper productF (addF productF productF) productF productF
    c (addData a b) b b hc (add_fast _ _ _ _ ha hb) hb hb expanded (cross_refl _ _ hb)
  have survive := GaussianNamedStrictOrderDifference.sum_sub_right productF productF a b ha hb
  have eq := cross_trans (F productF productF) (F (addF productF productF) productF) productF
    (X c b) (X (addData a b) b) a cancel survive
  have unitProduct := GaussianNameRingLaws.multiply_unit_left constantF logF qone x x
    (constant_regular _) hx (GaussianNameRingLaws.constant_one_cross x)
  exact cross_trans (F productF productF) productF logF (X c b) a x eq unitProduct

theorem actual_Euler_logarithm_weighted_unit_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ le one (var 4)) ⟶ crossEquivalent (F productF productF) logF
      (X (productData (var 0+var 2) (var 1) (var 2) (var 3) (var 4))
        (productData (var 0) (var 1) (var 2) (var 3) (var 4))) (L (var 4) one)) :=
  closeUniv 5 (.impI (difference _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerProductShift
