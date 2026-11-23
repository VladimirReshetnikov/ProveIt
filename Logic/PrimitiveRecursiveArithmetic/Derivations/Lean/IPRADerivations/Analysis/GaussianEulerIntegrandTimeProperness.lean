import IPRADerivations.Analysis.GaussianEulerPowerInputProperness
import IPRADerivations.Analysis.GaussianGammaWeierstrassApproximant

/-!
# Original normalized Euler integrands at equal positive rational times

The actual positive fractions and negative decay inputs are canonically
equal. The unchanged power-exponent names are equivalent through the
original logarithm properness theorem. Actual normalized addition and
independent original exponential radii then compare the full integrands.
No equality of original logarithm samples or their query clocks is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrandTimeProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (nameF data sample evaluatorF fixedData timeData powerExponentF powerExponentData
  exponentF exponentData radius decayPoint decayF decayData)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianPositiveRationalLogarithm (source fraction)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical represents_congr canonical_unique positive_product)
open GaussianRationalSyntheticDivision (rescale_to)
open ComplexLogarithmRemainder (scale oneCode)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_at)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalDistanceOrder (distance_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fraction_proper (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    fraction a b ≐ fraction c d := by
  let E := b*d
  have hE := positive_product b d hb hd
  have left := rescale_to (fraction a b) (scale a oneCode) b d E (ofGaussian_represents _ _ hb) (.eqRefl _)
  have right := rescale_to (fraction c d) (scale c oneCode) d b E (ofGaussian_represents _ _ hd) (by dsimp only [E]; ipra_ring)
  apply canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hb) (ofGaussian_canonical _ _ hd) hE (hrv := right)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) left
  apply GaussianRootAlgebra.equal_of_values
  · have eq := natEq he
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    linear_combination eq
  · simp only [GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one]
    ring

theorem decay_point_proper (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    decayPoint a b ≐ decayPoint c d :=
  GaussianInverseBinomialRows.negative_congr (fraction_proper a b c d hb hd he)

theorem decay_data_proper (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    decayData a b ≐ decayData c d := by
  simpa only [decayData,GaussianGammaFiniteApproximantName.exponentialInputData,GaussianRadiusExponentialName.subst_data,
    GaussianNameBounds.subst_U,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (Γ := Γ) (GaussianGammaFiniteApproximantName.exponentialInputData constantF (var 0) : PTm 1)
      (σ := ![decayPoint a b]) (σ' := ![decayPoint c d])
      (fun i => by fin_cases i; exact decay_point_proper a b c d hb hd he)

theorem decay_observation_equal (p a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    ap2 decayF p (decayData a b) ≐ ap2 decayF p (decayData c d) :=
  congrAp2 decayF (.eqRefl _) (decay_data_proper a b c d hb hd he)

theorem exponent_proper (z B a b c d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    crossEquivalent exponentF exponentF (exponentData z B a b) (exponentData z B c d) :=
  GaussianNameArithmetic.add_equivalent powerExponentF powerExponentF constantF constantF
    (powerExponentData z B a b) (powerExponentData z B c d) (decayPoint a b) (decayPoint c d)
    (GaussianEulerIntegrandName.power_exponent_regular z B a b (.andI hB hab))
    (GaussianEulerIntegrandName.power_exponent_regular z B c d (.andI hB hcd))
    (constant_regular _) (constant_regular _)
    (cross_to_diagonal _ _ _ _ (GaussianEulerPowerInputProperness.exponent_proper z B a b c d hab hcd he))
    (cross_to_diagonal _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_data_cross _ _
      (decay_point_proper a b c d hab.andE₂ hcd.andE₂ he)))

/-- The full original PR2 integrands retain their independently computed
input clocks, normalization queries, Taylor cutoffs and radii. -/
theorem original_integrand_proper (z B a b c d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z B a b) (data z B c d) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper exponentF exponentF
    (radius z B a b) (radius z B c d) (exponentData z B a b) (exponentData z B c d)
    (GaussianEulerIntegrandName.exponent_input z B a b (.andI hB hab))
    (GaussianEulerIntegrandName.exponent_input z B c d (.andI hB hcd)) (exponent_proper z B a b c d hB hab hcd he)

theorem original_rescale (z B a b E : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] source a b) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z B (a*E) (b*E)) (data z B a b) :=
  original_integrand_proper z B _ _ _ _ hB
    (.andI (positive_product _ _ hab.andE₁ hE) (positive_product _ _ hab.andE₂ hE)) hab (by ipra_ring)

theorem original_name_observations (p q z B a b c d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 nameF p (data z B a b)) (ap2 nameF q (data z B c d))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_integrand_proper z B a b c d hB hab hcd he)

theorem original_observations (p q z B a b c d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (sample p z B a b) (sample q z B c d)
      (unit p+unit q) (unit p*unit q) :=
  distance_congr (GaussianEulerIntegrandName.sample_at p z B a b).eqSymm
    (GaussianEulerIntegrandName.sample_at q z B c d).eqSymm (.eqRefl _) (.eqRefl _)
    (original_name_observations p q z B a b c d hB hab hcd he)

theorem actual_original_Euler_integrand_rational_time_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ source (var 2) (var 3) ⋏ source (var 4) (var 5) ⋏ var 2*var 5 ≐ var 3*var 4) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_integrand_proper _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

theorem actual_original_Euler_integrand_time_rescale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 1) ⋏ source (var 2) (var 3) ⋏ le one (var 4)) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 2*var 4) (var 3*var 4))
        (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (original_rescale _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_original_Euler_PR3_independent_time_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 3) ⋏ source (var 4) (var 5) ⋏ source (var 6) (var 7) ⋏ var 4*var 7 ≐ var 5*var 6) ⟶
      GaussianRationalMetric.distanceBounded
        (ap3 evaluatorF (var 0) (timeData (var 4) (var 5)) (fixedData (var 2) (var 3)))
        (ap3 evaluatorF (var 1) (timeData (var 6) (var 7)) (fixedData (var 2) (var 3)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (original_observations _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrandTimeProperness
