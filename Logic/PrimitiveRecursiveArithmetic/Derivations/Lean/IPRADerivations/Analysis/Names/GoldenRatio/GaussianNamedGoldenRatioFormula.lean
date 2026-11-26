import IPRADerivations.Analysis.Names.GoldenRatio.GaussianNamedGoldenRatio

/-!
# Exact named identification of the golden-ratio formula

The literal affine samples of the square-root bracket agree with the
independent original addition and multiplication names for
`(1+sqrt(5))/2`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatioFormula

open_ipra
open GaussianNamedGoldenRatio (onePoint)
open GaussianNamedSqrtFive (clock root)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev sqrtF : PR 2 := GaussianNamedSqrtFive.nameF
abbrev sumF : PR 2 := addF sqrtF constantF
abbrev nameF : PR 2 := multiplyF constantF sumF
def half : PTm n := fraction one two
def data (x : PTm n) : PTm n := multiplyData constantF sumF half (addData x onePoint)
def allowance (x : PTm n) : PTm n :=
  (multiplyModulus constantF sumF half (addData x onePoint)+one)+one*(two+one)

theorem affine_sample (p x : PTm n) : Γ ⊢[PRAAx]
    qmul (half : PTm n) (qadd (ap2 sqrtF p x) onePoint) ≐ GaussianNamedGoldenRatio.sample p := by
  let t := clock p
  let H := unit t
  let j := root t
  have hH : Γ ⊢[PRAAx] le one H := unit_positive t
  have sum : Γ ⊢[PRAAx] qadd (ap2 sqrtF p x) onePoint ≐ fraction (H+j) H :=
    (GaussianRationalSyntheticDivision.qadd_congr (GaussianNamedSqrtFive.sample_at p x) (.eqRefl _)).eqTrans
      ((GaussianEulerPositivePowerChartCorrectedImage.fraction_sum j H one one hH (le_refl one)).eqTrans
        (GaussianEulerPositivePowerChartJacobian.fraction_congr (by ipra_ring) (by ipra_ring)))
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) sum).eqTrans
    ((GaussianEulerDampedTimeRate.fraction_product one two (H+j) H (le_succ_self one) hH).eqTrans
      (GaussianEulerPositivePowerChartJacobian.fraction_congr (one_mul _) (.eqRefl _)))

theorem observation (p x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data x)) (ap2 GaussianNamedGoldenRatio.nameF p x) (allowance x) (unit p) := by
  let s := addData x onePoint
  have hU : Γ ⊢[PRAAx] le one (unit p) := unit_positive p
  have sq := GaussianNamedSqrtFive.name_regular (Γ := Γ) x
  have hsum := GaussianNameArithmetic.add_fast sqrtF constantF x onePoint sq (constant_regular _)
  have prod := GaussianNameRingLaws.multiply_sample_error constantF sumF (half : PTm n) s p (constant_regular _) hsum
  have fixed := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p half) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) prod
  have sum := GaussianNameRingLaws.add_sample_error sqrtF constantF x onePoint p sq (constant_regular _)
  have raw := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (constant_at p onePoint))
    (.eqRefl _) (.eqRefl _) sum
  have bound := GaussianEulerExponentCompactBounds.fraction_bound (Γ := Γ) one two one (le_succ_self one)
    (le_congr (.eqRefl _) (one_mul two).eqSymm (le_succ_self one))
  have scaled := GaussianApproximateInverseDistance.multiply_distance (half : PTm n) _ _ one _ _ hU bound raw
  have result := distance_triangle_same _ _ _ _ _ _ hU fixed scaled
  exact distance_congr (.eqRefl _) ((affine_sample p x).eqTrans (GaussianNamedGoldenRatio.sample_at p x).eqSymm)
    (.eqRefl _) (.eqRefl _) result

theorem original_formula (x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianNamedGoldenRatio.nameF (data x) x := by
  have sq := GaussianNamedSqrtFive.name_regular (Γ := Γ) x
  have sum := GaussianNameArithmetic.add_fast sqrtF constantF x onePoint sq (constant_regular _)
  have diag : Γ ⊢[PRAAx] diagonalRate nameF GaussianNamedGoldenRatio.nameF (data x) x (allowance x) := by
    refine .allI ?_
    simpa [diagonalRate,data,allowance,half,onePoint,Syn.shift] using
      (observation (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x))
  exact cross_of_diagonal_rate _ _ _ _ _
    (GaussianNameArithmetic.multiply_fast _ _ _ _ (constant_regular _) sum)
    (GaussianNamedGoldenRatio.name_regular _) diag

theorem actual_independent_named_golden_ratio_formula_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent nameF GaussianNamedGoldenRatio.nameF (data (var 0)) (var 0)) :=
  closeUniv 1 (original_formula _)

end LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatioFormula
