import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinDampedImproper
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerPowerRebasing
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# The original Dirichlet row at reciprocal time

For every positive n, the original exponential of -s log(n) agrees
with the original Euler power at time 1/n multiplied by 1/n. Both
programs use the original normalized arithmetic and independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletReciprocalRow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerPositiveScalingConstant (exponentF exponentData inverseF inverseData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_equivalent
  negative_sample_error multiply_sample_error three)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric)
open GaussianRationalHorner (ofGaussian qmul)
open GaussianRationalMetric (qnegative qnegative_canonical distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qzero_add)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianHarmonicLogarithmName.nameF
local notation "Log" => GaussianPositiveRationalLogarithm.logF

private abbrev weightedF : PR 2 := multiplyF constantF L
private def weightedData (c a b : PTm n) : PTm n :=
  multiplyData constantF L c (GaussianHarmonicLogarithmName.data a b)
private def signBudget (c a b : PTm n) : PTm n :=
  (three+(multiplyModulus constantF L c (GaussianHarmonicLogarithmName.data a b)+one))+
    (multiplyModulus constantF L c (GaussianHarmonicLogarithmName.data b a)+one)

private theorem weighted_regular (c a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] pointCN weightedF (weightedData c a b) :=
  multiply_fast constantF L c _ (constant_regular c) (GaussianHarmonicLogarithmName.name_regular a b h)

private theorem weighted_reciprocal_at (p c a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (negativeF weightedF) p (negativeData (weightedData c a b)))
      (ap2 weightedF p (weightedData c b a)) (signBudget c a b) (unit p) := by
  let x := GaussianHarmonicLogarithmName.data a b
  let y := GaussianHarmonicLogarithmName.data b a
  let u := ap2 L p x
  let v := ap2 L p y
  let A := ap2 weightedF p (weightedData c a b)
  have hc := constant_regular (Γ := Γ) c
  have hd := unit_positive (Γ := Γ) p
  have left := distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl u)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error constantF L c x p hc (GaussianHarmonicLogarithmName.name_regular a b h))
  have negated := GaussianNamedDifference.negative_distance A (qmul c u) _ _ hd left
  have small := distance_congr (.eqRefl _) (qzero_add _ (qnegative_canonical A)) (.eqRefl _) (.eqRefl _)
    (negative_sample_error weightedF (weightedData c a b) p (weighted_regular c a b h))
  have e : Γ ⊢[PRAAx] qnegative (qmul c u) ≐ qmul c v :=
    (GaussianInverseBinomialRows.negative_product c u).eqTrans
      ((GaussianEulerLowerRationalPowerReference.negative_move c u).eqTrans
        (qmul_congr (.eqRefl c) (GaussianEulerLowerPowerRebasing.reciprocal_sample p a b)))
  have right := distance_congr (.eqRefl _) ((qmul_congr (constant_at p c) (.eqRefl v)).eqTrans e.eqSymm)
    (.eqRefl _) (.eqRefl _) (multiply_sample_error constantF L c y p hc
      (GaussianHarmonicLogarithmName.name_regular b a (.andI h.andE₂ h.andE₁)))
  exact distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd small negated)
    (distance_symmetric _ _ _ _ hd right)

private theorem weighted_reciprocal (c a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF weightedF) weightedF
      (negativeData (weightedData c a b)) (weightedData c b a) := by
  refine cross_of_diagonal_rate _ _ _ _ (signBudget c a b)
    (negative_fast _ _ (weighted_regular c a b h)) (weighted_regular c b a (.andI h.andE₂ h.andE₁)) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [diagonalRate,weightedData,signBudget,Syn.shift,three,one] using
    weighted_reciprocal_at (var 0) (Syn.shift c) (Syn.shift a) (Syn.shift b) hs

private theorem original_weighted (z B a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerPositiveScalingConstant.source B a b) :
    Γ ⊢[PRAAx] crossEquivalent exponentF weightedF (exponentData z B a b) (weightedData (ofGaussian z B) a b) := by
  let c := ofGaussian z B
  have hc := constant_regular (Γ := Γ) c
  exact multiply_cross constantF constantF Log L c c _ _ hc hc
    (GaussianPositiveRationalLogarithm.name_regular a b h.andE₂)
    (GaussianHarmonicLogarithmName.name_regular a b h.andE₂) (cross_refl _ _ hc)
    (GaussianHarmonicLogarithmName.cross_original a b h.andE₂)

theorem inverse_exponent_reciprocal (z B a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerPositiveScalingConstant.source B a b) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF exponentF) exponentF
      (negativeData (exponentData z B a b)) (exponentData z B b a) := by
  let c := ofGaussian z B
  have e := original_weighted z B a b h
  have e' := original_weighted z B b a (.andI h.andE₁ (.andI h.andE₂.andE₂ h.andE₂.andE₁))
  have neg := negative_equivalent exponentF weightedF _ _
    (GaussianEulerPositiveScalingConstant.exponent_regular z B a b h)
    (weighted_regular c a b h.andE₂) (cross_to_diagonal _ _ _ _ e)
  exact cross_trans _ _ _ _ _ _ neg
    (cross_trans _ _ _ _ _ _ (weighted_reciprocal c a b h.andE₂) (cross_symm _ _ _ _ e'))

theorem inverse_reciprocal (z B a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerPositiveScalingConstant.source B a b) :
    Γ ⊢[PRAAx] crossEquivalent inverseF GaussianEulerPositiveScalingConstant.nameF
      (inverseData z B a b) (GaussianEulerPositiveScalingConstant.data z B b a) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (GaussianEulerPositiveScalingConstant.inverse_input z B a b h)
    (GaussianEulerPositiveScalingConstant.original_input z B b a
      (.andI h.andE₁ (.andI h.andE₂.andE₂ h.andE₂.andE₁))) (inverse_exponent_reciprocal z B a b h)

abbrev reciprocalRowF : PR 2 := GaussianEulerPositiveScalingConstant.scaleF
def reciprocalRowData (z B j : PTm n) : PTm n :=
  GaussianEulerPositiveScalingConstant.scaleData z B one j

/-- The actual n-th finite Dirichlet term has the reciprocal Euler-power representation. -/
theorem dirichlet_row_reciprocal (z B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent inverseF reciprocalRowF (inverseData z B j one) (reciprocalRowData z B j) :=
  cross_trans _ _ _ _ _ _ (inverse_reciprocal z B j one (.andI hB (.andI hj (le_refl one))))
    (GaussianEulerPositiveScalingConstant.original_scaling_constant_symm z B one j (.andI hB (.andI (le_refl one) hj)))

theorem actual_original_Dirichlet_reciprocal_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ crossEquivalent inverseF reciprocalRowF
      (inverseData (var 0) (var 1) (var 2) one) (reciprocalRowData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (dirichlet_row_reciprocal _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletReciprocalRow
