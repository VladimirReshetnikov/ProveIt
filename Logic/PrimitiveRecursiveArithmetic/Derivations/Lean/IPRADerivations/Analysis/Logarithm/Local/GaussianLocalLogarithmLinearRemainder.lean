import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmName
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale

/-!
# Actual local logarithm and scaled quadratic remainder

The original finite C3 factor and actual unshifted logarithm rounding
prove |log(1+z/D)-z/D| <=R^2/D^2+eps_p. Actual existing natural-scale
clocks preserve only eps_p after scaling. This supplies the quantitative
logarithm step for the finite beta kernel; no logarithm/output law or
analytic limit is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLocalLogarithmLinearRemainder

open_ipra
open GaussianLocalLogarithmName (source pointF point)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GammaCanonicalFactors (factorNumerator factorDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem finite_factor_bound (z R D L : PTm n) (h : Γ ⊢[PRAAx] source z R D) : Γ ⊢[PRAAx]
    bounded (GammaLogarithmFactorBridge.localFactor z D L) (R*R) (D*D) := by
  have hd := GammaCanonicalFactors.factorDenominator_positive D L h.andE₁
  have old := GammaCanonicalFactors.finite_factor_bound z D R L h.andE₂.andE₁ h.andE₁ h.andE₂.andE₂
  have cleared : Γ ⊢[PRAAx] le ((D*D)*(D*D)*ComplexLogarithmRemainder.normSq (factorNumerator z D L))
      ((R*R)*(R*R)*(factorDenominator D L*factorDenominator D L)) :=
    le_congr (ComplexLogarithmRemainder.normSq_scale _ _) (by ipra_ring) old
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hd (positive_product _ _ h.andE₁ h.andE₁)
    (ofGaussian_represents _ _ hd) cleared

theorem finite_linear_remainder (z R D L : PTm n) (h : Γ ⊢[PRAAx] source z R D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianFiniteLogarithmSampler.sample z D L) (ofGaussian z D) (R*R) (D*D) := by
  have e := (GaussianRationalSyntheticDivision.qsub_congr
    (GammaLogarithmFactorBridge.sum_is_original_sample z D L h.andE₁).eqSymm (.eqRefl (ofGaussian z D))).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (ofGaussian_canonical _ _
        (GammaCanonicalFactors.factorDenominator_positive D L h.andE₁)))
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) (finite_factor_bound z R D L h)

/-- The old observation is kept at its original precision. Its true
4/2^(p+4) rounding error is absorbed into the requested eps_p. -/
theorem original_linear_remainder (p z R D : PTm n) (h : Γ ⊢[PRAAx] source z R D) : Γ ⊢[PRAAx]
    distanceBounded (point p z R D) (ofGaussian z D)
      (R*R*unit p+D*D) (D*D*unit p) := by
  have hu := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  have u := unit_positive (Γ := Γ) p
  have dd := positive_product (Γ := Γ) _ _ h.andE₁ h.andE₁
  have scale : Γ ⊢[PRAAx] le (num 4*unit p) (DyadicComplexLogarithm.unit p) :=
    le_congr (.eqRefl _) (GaussianLocalLogarithmName.unit_factor p).eqSymm
      (le_of_eq_add (d := num 12*unit p) (by ipra_ring))
  have round := distance_radius_mono _ _ _ _ one (unit p) hu u (le_congr (.eqRefl _) (one_mul _).eqSymm scale)
    (GaussianLocalLogarithmName.point_rounding_distance p z R D h.andE₁)
  have finite := finite_linear_remainder z R D (DyadicComplexLogarithm.precision p) h
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (mul_comm _ _)
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ u dd round finite)

theorem linear_unit_bound (z R D : PTm n) (h : Γ ⊢[PRAAx] source z R D) : Γ ⊢[PRAAx]
    bounded (ofGaussian z D) one one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_succ_self one) (le_refl _)
    (le_of_eq_add (d := one) (by ipra_ring))
    (GaussianFiniteLogarithmCompositionName.original_half_disk z R D h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)

/-- Actual capped natural-scale observations; its computed clock absorbs
exactly the multiplication of the ordinary logarithm observation error. -/
theorem scaled_linear_remainder (p E M z R D : PTm n) (h : Γ ⊢[PRAAx] source z R D) (hm : Γ ⊢[PRAAx] le M E) : Γ ⊢[PRAAx]
    distanceBounded (GaussianNamedNaturalScale.sample pointF p E M (GaussianLocalLogarithmName.data z R D))
      (GaussianRationalNaturalScale.natScale M (ofGaussian z D))
      (M*R*R*unit p+D*D) (D*D*unit p) := by
  let r := GaussianNamedNaturalScale.clock p E
  have den := positive_product (Γ := Γ) _ _ (positive_product _ _ h.andE₁ h.andE₁) (unit_positive r)
  have old := GaussianNamedNaturalScale.scaled_distance M _ _ (R*R*unit r+D*D) (D*D*unit r) one den
    (original_linear_remainder r z R D h) (linear_unit_bound z R D h)
  have clockBudget : Γ ⊢[PRAAx] le (M*unit p) (unit r) :=
    le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (GaussianNamedNaturalScale.clock_unit p E).eqSymm)
      (mul_le_mul_right (unit p) (GaussianNamedNaturalScale.cap_budget E M hm))
  have clear := add_le_add_right (M*R*R*unit r*(D*D*unit p)) (mul_le_mul_right (D*D*(D*D)) clockBudget)
  exact distance_congr (GaussianNamedNaturalScale.sample_at pointF p E M _).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ (M*R*R*unit p+D*D) (D*D*unit p) den
      (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) (unit_positive p))
      (le_congr (by ipra_ring) (by ipra_ring) clear) old)

theorem actual_finite_logarithm_quadratic_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ distanceBounded (GaussianFiniteLogarithmSampler.sample (var 0) (var 2) (var 3))
      (ofGaussian (var 0) (var 2)) (var 1*var 1) (var 2*var 2)) :=
  closeUniv 4 (.impI (finite_linear_remainder _ _ _ _ Prf.hyp0))
theorem original_local_logarithm_quadratic_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ distanceBounded (point (var 0) (var 1) (var 2) (var 3))
      (ofGaussian (var 1) (var 3)) (var 2*var 2*unit (var 0)+var 3*var 3) (var 3*var 3*unit (var 0))) :=
  closeUniv 4 (.impI (original_linear_remainder _ _ _ _ Prf.hyp0))
theorem actual_scaled_local_logarithm_quadratic_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 3) (var 4) (var 5) ⟶ le (var 2) (var 1) ⟶ distanceBounded
      (GaussianNamedNaturalScale.sample pointF (var 0) (var 1) (var 2) (GaussianLocalLogarithmName.data (var 3) (var 4) (var 5)))
      (GaussianRationalNaturalScale.natScale (var 2) (ofGaussian (var 3) (var 5)))
      (var 2*var 4*var 4*unit (var 0)+var 5*var 5) (var 5*var 5*unit (var 0))) :=
  closeUniv 6 (.impI (.impI (scaled_linear_remainder _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLocalLogarithmLinearRemainder
