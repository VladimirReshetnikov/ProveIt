import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadShift
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaWeierstrassApproximant
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# Finite shift of the original Euler approximants

The actual harmonic-mesh exponent at the shifted argument equals the
sum of the original exponent and the negative mesh logarithm. Combined
with the exact shift of the original Euler head, this yields the finite
shift identity with the actual exponential of minus the logarithm.
The identity holds at zeros and uses no division by the input argument.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerShift

open_ipra
open GaussianGammaEulerHeadShift (shifted linear returned_shift_identity)
open GaussianRationalHorner (qadd qmul ofGaussian ofGaussian_represents positive_product represents_congr canonical_unique)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalMatrixFiniteSums (minusOne)
open GaussianRationalMetric (qnegative qnegative_represents)
open GaussianRootAlgebra (equal_of_values re_neg im_neg re_add im_add re_scale im_scale)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName
  (logF log_regular logExponentF logExponentData log_exponent_regular exponential_input exponentialInputData
    qF qData q_regular approximantData)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameRingLaws (multiply_associative distributive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans diagonalEquivalent diagonal_to_cross)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem negative_shift (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qnegative (ofGaussian (shifted z B) B) ≐ qadd (qnegative (ofGaussian z B)) minusOne := by
  have left := qnegative_represents _ _ _ (ofGaussian_represents (shifted z B) B hB)
  have right := GaussianRationalHorner.qadd_represents _ _ _ _ _ hB
    (qnegative_represents _ _ _ (ofGaussian_represents z B hB))
    (qnegative_represents _ _ _ (GaussianRationalReciprocal.qone_represents_scaled B))
  refine canonical_unique _ _ _ _ (GaussianRationalMetric.qnegative_canonical _)
    (GaussianRationalHorner.qadd_canonical _ _) hB ?_ right
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) left
  apply equal_of_values <;> simp only [shifted,GaussianGammaEulerHeadLower.translated,re_neg,im_neg,re_add,im_add,re_scale,im_scale] <;>
    (try ipra_simps) <;> ring

theorem constant_sum_cross (x y : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (addF constantF constantF) constantF (addData x y) (qadd x y) := by
  have primary : Γ ⊢[PRAAx] pointCN (addF constantF constantF) (addData x y) :=
    add_fast _ _ _ _ (constant_regular _) (constant_regular _)
  refine diagonal_to_cross _ _ _ _ primary (constant_regular _) (.allI ?_)
  let C := Γ.map Fm.shift
  let a := Syn.shift x
  let b := Syn.shift y
  let p : PTm (n+1) := var 0
  have eq : C ⊢[PRAAx] ap2 (addF constantF constantF) p (addData a b) ≐ ap2 constantF p (qadd a b) :=
    (GaussianNameArithmetic.add_at constantF constantF a b p).eqTrans
      ((GaussianNameArithmetic.recode_congr (qadd_congr (constant_at _ _) (constant_at _ _))).eqTrans
        ((GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)).eqTrans
          (constant_at p (qadd a b)).eqSymm))
  have close : C ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (ap2 (addF constantF constantF) p (addData a b)) (ap2 constantF p (qadd a b)) two (unit p) :=
    distance_radius_mono _ _ zero (unit p) two (unit p) (unit_positive _) (unit_positive _)
      (le_congr (by ipra_ring) (.eqRefl _) (zero_le _))
      (distance_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (GaussianRationalPowerDifference.distance_refl_zero _ _ (unit_positive p)))
  simpa only [diagonalEquivalent,Syn.shift,GaussianNameArithmetic.subst_addData,GaussianRationalHorner.subst_qadd,
    GaussianEuclideanPointDistance.unit,C,a,b,p] using close

def negativeLogData (N : PTm n) : PTm n := multiplyData logF constantF N minusOne
def expF : PR 2 := GaussianRadiusExponentialName.nameF logExponentF
def negativeLogExpData (N : PTm n) : PTm n := exponentialInputData logExponentF (negativeLogData N)

theorem negative_log_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN logExponentF (negativeLogData N) :=
  multiply_fast _ _ _ _ (log_regular _ hN) (constant_regular _)

theorem negative_log_exp_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN expF (negativeLogExpData N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (negative_log_regular N hN))

theorem exponent_shift (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent (addF logExponentF logExponentF) logExponentF
      (addData (logExponentData z B N) (negativeLogData N)) (logExponentData (shifted z B) B N) := by
  let a := qnegative (ofGaussian z B)
  let b : PTm n := minusOne
  let c := qnegative (ofGaussian (shifted z B) B)
  let hl := log_regular N hN
  have ca := constant_regular (Γ := Γ) a
  have cb := constant_regular (Γ := Γ) b
  have cs := constant_sum_cross (Γ := Γ) a b
  have hconst := cross_trans _ _ _ _ _ _ cs (constant_data_cross _ _ (negative_shift z B hB).eqSymm)
  have e := multiply_cross logF logF (addF constantF constantF) constantF N N (addData a b) c
    hl hl (add_fast _ _ _ _ ca cb) (constant_regular c) (cross_refl _ _ hl) hconst
  have dist := distributive logF constantF constantF N a b hl ca cb
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ dist) e

theorem merge_head (e : PR 2) (x y v : PTm n) (h : Γ ⊢[PRAAx] pointCN e v) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF (multiplyF constantF e)) (multiplyF constantF e)
      (multiplyData constantF (multiplyF constantF e) x (multiplyData constantF e y v))
      (multiplyData constantF e (qmul x y) v) := by
  have a := multiply_associative constantF constantF e x y v (constant_regular _) (constant_regular _) h
  have b := multiply_cross (multiplyF constantF constantF) constantF e e (multiplyData constantF constantF x y)
    (qmul x y) v v (multiply_fast _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _)
    h h (constant_product_cross x y) (cross_refl _ _ h)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ a) b

def leftF : PR 2 := multiplyF constantF qF
def leftData (z B N : PTm n) : PTm n := multiplyData constantF qF (ofGaussian z B) (qData (shifted z B) B N)
def rightF : PR 2 := multiplyF constantF (multiplyF qF expF)
def rightData (z B N : PTm n) : PTm n :=
  multiplyData constantF (multiplyF qF expF) (linear z B (succ N))
    (multiplyData qF expF (qData z B N) (negativeLogExpData N))

theorem finite_shift (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent leftF rightF (leftData z B N) (rightData z B N) := by
  let w := shifted z B
  let H := GaussianGammaEulerHead.run z B N
  let J := GaussianGammaEulerHead.run w B N
  let c := linear z B (succ N)
  let x := ofGaussian z B
  let y := exponentialInputData logExponentF (logExponentData w B N)
  have ey := GaussianRadiusExponentialName.name_regular _ _ _
    (exponential_input _ _ (log_exponent_regular w B N hN))
  have a := merge_head expF x J y ey
  have eq := returned_shift_identity z B N hB
  have b := merge_head expF c H y ey
  have ab := multiply_cross constantF constantF expF expF (qmul x J) (qmul c H) y y
    (constant_regular _) (constant_regular _) ey ey
    (constant_data_cross _ _ (eq.eqTrans (GaussianRationalPowerAlgebra.qmul_commutative H c))) (cross_refl _ _ ey)
  have h := GaussianGammaFoldedApproximantBalance.approximant_product_equivalent logExponentF logExponentF logExponentF
    (logExponentData z B N) (negativeLogData N) (logExponentData w B N) z B N
    (log_exponent_regular z B N hN) (negative_log_regular N hN) (log_exponent_regular w B N hN) (exponent_shift z B N hB hN)
  have tail := multiply_cross constantF constantF qF (multiplyF qF expF) c c
    (approximantData logExponentF (logExponentData w B N) z B N)
    (multiplyData qF expF (qData z B N) (negativeLogExpData N)) (constant_regular c) (constant_regular c)
    (multiply_fast _ _ _ _ (constant_regular H) ey)
    (multiply_fast _ _ _ _ (q_regular z B N hN) (negative_log_exp_regular N hN))
    (cross_refl _ _ (constant_regular c)) (cross_symm _ _ _ _ h)
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ ab
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ b) tail))

theorem original_Euler_exponent_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ crossEquivalent (addF logExponentF logExponentF) logExponentF
      (addData (logExponentData (var 0) (var 1) (var 2)) (negativeLogData (var 2)))
      (logExponentData (shifted (var 0) (var 1)) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (exponent_shift _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_finite_Euler_approximant_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ crossEquivalent leftF rightF
      (leftData (var 0) (var 1) (var 2)) (rightData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (finite_shift _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerShift
