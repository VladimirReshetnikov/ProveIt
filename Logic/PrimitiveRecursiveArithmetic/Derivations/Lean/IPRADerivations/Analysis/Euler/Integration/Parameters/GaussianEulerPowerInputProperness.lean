import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandName
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff

/-!
# Original Euler time-power names respect rational time encodings

Actual original logarithm properness is transported through the unchanged
constant product and both independently computed exponential radii. This
compares the actual original observations at arbitrary independent clocks;
no equality of rounded samples or output values is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerInputProperness

open_ipra
open GaussianEulerIntegrandName (powerF powerData powerExponentF powerExponentData powerRadius coefficient logarithmF)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianPositiveRationalLogarithm (source name_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_at)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exponent_proper (z B a b c d : PTm n)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    crossEquivalent powerExponentF powerExponentF (powerExponentData z B a b) (powerExponentData z B c d) :=
  GaussianGammaAdjacentCutoff.multiply_cross constantF constantF logarithmF logarithmF
    (coefficient z B) (coefficient z B) (GaussianPositiveRationalLogarithm.data a b) (GaussianPositiveRationalLogarithm.data c d)
    (constant_regular _) (constant_regular _) (name_regular a b hab) (name_regular c d hcd)
    (cross_refl constantF _ (constant_regular _))
    (GaussianPositiveRationalLogarithmProperness.original_logarithm_proper a b c d hab hcd he)

theorem original_power_proper (z B a b c d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    crossEquivalent powerF powerF (powerData z B a b) (powerData z B c d) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper powerExponentF powerExponentF
    (powerRadius z B a b) (powerRadius z B c d) (powerExponentData z B a b) (powerExponentData z B c d)
    (GaussianEulerIntegrandName.power_input z B a b (.andI hB hab))
    (GaussianEulerIntegrandName.power_input z B c d (.andI hB hcd)) (exponent_proper z B a b c d hab hcd he)

theorem original_power_rescale (z B a b E : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] source a b) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    crossEquivalent powerF powerF (powerData z B (E*a) (E*b)) (powerData z B a b) :=
  original_power_proper _ _ _ _ _ _ hB (.andI (positive_product _ _ hE hab.andE₁) (positive_product _ _ hE hab.andE₂)) hab (by ipra_ring)

theorem original_power_observations (p q z B a b c d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hab : Γ ⊢[PRAAx] source a b) (hcd : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 powerF p (powerData z B a b)) (ap2 powerF q (powerData z B c d))
      (unit p+unit q) (unit p*unit q) :=
  cross_at powerF powerF _ _ p q (original_power_proper z B a b c d hB hab hcd he)

theorem original_Euler_power_rational_input_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ source (var 2) (var 3) ⋏ source (var 4) (var 5) ⋏ var 2*var 5 ≐ var 3*var 4) ⟶
      crossEquivalent powerF powerF (powerData (var 0) (var 1) (var 2) (var 3)) (powerData (var 0) (var 1) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_power_proper _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem original_Euler_power_denominator_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 1) ⋏ source (var 2) (var 3) ⋏ le one (var 4)) ⟶
      crossEquivalent powerF powerF (powerData (var 0) (var 1) (var 4*var 2) (var 4*var 3))
        (powerData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (original_power_rescale _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_original_Euler_power_independent_encoding_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 3) ⋏ source (var 4) (var 5) ⋏ source (var 6) (var 7) ⋏ var 4*var 7 ≐ var 5*var 6) ⟶
      GaussianRationalMetric.distanceBounded (ap2 powerF (var 0) (powerData (var 2) (var 3) (var 4) (var 5)))
        (ap2 powerF (var 1) (powerData (var 2) (var 3) (var 6) (var 7)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (original_power_observations _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerInputProperness
