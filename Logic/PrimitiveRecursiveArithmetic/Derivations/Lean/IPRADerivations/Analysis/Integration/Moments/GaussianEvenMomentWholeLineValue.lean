import IPRADerivations.Analysis.Integration.Moments.GaussianEvenMomentWholeLine
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartCorrectedImage

/-!
# Explicit unhalved coefficient of the whole-line Gaussian moments

The two occurrences of the original factor 1/2 combine to the exact
constant one. The whole-line value is the original inverse positive
rational scaling power times the factorial coefficient and the
independently computed square root of π.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEvenMomentWholeLineValue

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaHalfIntegerDomain (argument)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianEulerPositiveScalingConstant (inverseF inverseData inverse_regular)
open GaussianRationalHorner (qadd)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalSyntheticDivision (qone qadd_congr qone_canonical)
open GaussianNameRingLaws (oneF one_at one_fast)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev factorialF : PR 2 := GaussianGammaHalfSqrtValues.valueF
abbrev valueF : PR 2 := multiplyF inverseF factorialF
def valueData (N c d x : PTm n) : PTm n := multiplyData inverseF factorialF
  (inverseData (argument N) two c d) (GaussianGammaHalfSqrtValues.valueData N x)

theorem half_sum : Γ ⊢[PRAAx] qadd (GaussianEulerSquareFactorInverse.half : PTm n) GaussianEulerSquareFactorInverse.half ≐ qone := by
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := zero_lt_succ one
  have den := GaussianRationalHorner.positive_product (Γ := Γ) _ _ h2 h2
  have sum := GaussianEulerPositivePowerChartCorrectedImage.fraction_sum (Γ := Γ) one two one two h2 h2
  exact sum.eqTrans
    ((GaussianCompactRiemannName.fraction_congr _ _ _ _
      (by ipra_ring : Γ ⊢[PRAAx] one*two+one*two ≐ (two*two)*one)
      (by ipra_ring : Γ ⊢[PRAAx] two*two ≐ (two*two)*one)).eqTrans
      ((GaussianCompactRiemannSplit.fraction_cancel (two*two) one one den (le_refl one)).eqTrans
        GaussianGammaFactorialValues.natural_one))

private theorem half_sum_at (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (addF constantF constantF) p (addData GaussianEulerSquareFactorInverse.half GaussianEulerSquareFactorInverse.half) ≐ ap2 oneF p x := by
  let q := GaussianFastValueCut.exponent two p
  have a := constant_at (Γ := Γ) q (GaussianEulerSquareFactorInverse.half : PTm n)
  have c := (qadd_congr a a).eqTrans (half_sum (Γ := Γ))
  exact (GaussianNameArithmetic.add_at constantF constantF GaussianEulerSquareFactorInverse.half GaussianEulerSquareFactorInverse.half p).eqTrans
    ((GaussianNameArithmetic.recode_congr c).eqTrans
      ((GaussianExponentialReference.recode_fixed _ qone_canonical).eqTrans (one_at p x).eqSymm))

theorem half_sum_cross (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent (addF constantF constantF) oneF (addData GaussianEulerSquareFactorInverse.half GaussianEulerSquareFactorInverse.half) x := by
  let h : PTm n := GaussianEulerSquareFactorInverse.half
  have reg : Γ ⊢[PRAAx] pointCN constantF h := constant_regular _
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (add_fast _ _ _ _ reg reg) (one_fast x)
  refine .allI ?_
  simpa only [h,GaussianNameConjugation.pointwiseEqual,GaussianNameArithmetic.subst_addData,
    GaussianEulerSquareFactorInverse.subst_half,Syn.shift] using
    half_sum_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)

set_option maxHeartbeats 1600000 in
theorem cancel_half_factors (N c d x : PTm n)
    (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEvenMomentWholeLine.valueF valueF (GaussianEvenMomentWholeLine.valueData N c d x)
      (valueData N c d x) := by
  let I := inverseData (argument N) two c d
  let H := GaussianGammaHalfSqrtValues.valueData N x
  let h : PTm n := GaussianEulerSquareFactorInverse.half
  let Y := valueData N c d x
  let G := multiplyF constantF valueF
  let Z := multiplyData constantF valueF h Y
  have hi := inverse_regular (argument N) two c d (.andI (zero_lt_succ one) (.andI hc hd))
  have hh : Γ ⊢[PRAAx] pointCN factorialF H :=
    multiply_fast _ _ _ _ (constant_regular _) (GaussianGammaHalfSqrtValues.sqrt_regular x)
  have hc' : Γ ⊢[PRAAx] pointCN constantF h := constant_regular _
  have hy : Γ ⊢[PRAAx] pointCN valueF Y := multiply_fast _ _ _ _ hi hh
  have assoc := GaussianNameRingLaws.multiply_associative constantF inverseF factorialF h I H hc' hi hh
  have old : Γ ⊢[PRAAx] pointCN GaussianGammaHalfSqrtValues.momentF (GaussianGammaHalfSqrtValues.momentData N c d x) :=
    multiply_fast _ _ _ _ (multiply_fast _ _ _ _ hc' hi) hh
  have new : Γ ⊢[PRAAx] pointCN G Z := multiply_fast _ _ _ _ hc' hy
  have move := GaussianNameArithmetic.add_equivalent GaussianGammaHalfSqrtValues.momentF G
    GaussianGammaHalfSqrtValues.momentF G _ Z _ Z old new old new
    (cross_to_diagonal _ _ _ _ assoc) (cross_to_diagonal _ _ _ _ assoc)
  have dist := GaussianNameRingLaws.right_distributive constantF constantF valueF h h Y hc' hc' hy
  have coef := GaussianGammaAdjacentCutoff.multiply_cross (addF constantF constantF) oneF
    valueF valueF (addData h h) Y Y Y (add_fast _ _ _ _ hc' hc') (one_fast Y) hy hy
    (half_sum_cross Y) (cross_refl _ _ hy)
  exact cross_trans _ _ _ _ _ _ move (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ dist)
    (cross_trans _ _ _ _ _ _ coef (GaussianNameRingLaws.multiply_one_left valueF Y hy)))

theorem original_whole_value (N c d x : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEvenMomentWholeLine.nameF valueF (GaussianEvenMomentWholeLine.data N c d)
      (valueData N c d x) :=
  cross_trans _ _ _ _ _ _ (GaussianEvenMomentWholeLine.original_even_whole_value N c d x hc hd)
    (cancel_half_factors N c d x hc hd)

theorem actual_original_whole_line_Gaussian_even_unhalved_value_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 1) ⟶ le one (var 2) ⟶ crossEquivalent GaussianEvenMomentWholeLine.nameF valueF
        (GaussianEvenMomentWholeLine.data (var 0) (var 1) (var 2))
        (valueData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (original_whole_value _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEvenMomentWholeLineValue
