import IPRADerivations.Analysis.Euler.PowerScaling.Named.Parameters.GaussianEulerNamedPowerScalingParameter
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedPositiveReciprocalFrozen

/-!
# Rescaled Gamma parameters at literal frozen exponent observations

The genuine named z/r has a uniform comparison to the original native
rescaled parameter using the exact decoded exponent. The upper and lower
disk guards use the same supplied bounds for every frozen index.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingParameterFrozen

open_ipra
open GaussianEulerNamedPowerScalingParameter (nameF data source regular)
open GaussianNamedPositiveLogarithm (numerator denominator decoded_domain)
open GaussianNamedPositiveReciprocalFrozen (frozen)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianRationalHorner (ofGaussian ofGaussian_represents)
open GaussianRationalMetric (bounded)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def frozenPoint (f : PR 2) (k z B x : PTm n) : PTm n :=
  ofGaussian (scaled z (denominator f k x)) (B*numerator f k x)

theorem original_frozen_source (f : PR 2) (k z R B A x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f z R B A x E T) : Γ ⊢[PRAAx]
    GaussianEulerIntegralGammaIdentification.source (scaled z (denominator f k x)) (E*R)
      (B*numerator f k x) (T*A) := by
  let a := numerator f k x
  let b := denominator f k x
  have h := decoded_domain f k x E T hs.andE₂.andE₂
  have input : Γ ⊢[PRAAx] GaussianEulerPowerScalingParameter.source z R B A a b E T :=
    .andI hs.andE₁ (.andI h.andE₁.andE₁ (.andI h.andE₁.andE₂
      (.andI hs.andE₂.andE₂.andE₂.andE₁ (.andI hs.andE₂.andE₁ h.andE₂))))
  exact GaussianEulerPowerScalingParameter.original_rescaled_source z R B A a b E T input

theorem original_frozen_rate (f : PR 2) (k z R B A x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f z R B A x E T) : Γ ⊢[PRAAx]
    independentRate (nameF f) constantF (data z R B x E) (frozenPoint f k z B x) (R*(E*E)) (unit k) := by
  let D := unit k
  let c := ofGaussian z B
  let inv := GaussianNamedPositiveReciprocal.nameF f
  let a := GaussianNamedPositiveReciprocal.data x E
  let b := frozen f k x
  let d := GaussianBoundedConstantProductName.data R c b
  let P := GaussianBoundedConstantProductName.nameF constantF
  have hd : Γ ⊢[PRAAx] le one D := unit_positive k
  have orig := hs.andE₁.andE₁.andE₂.andE₁
  have coeff : Γ ⊢[PRAAx] bounded c R one :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ orig.andE₁ (le_refl one)
      (ofGaussian_represents z B orig.andE₁) (le_congr (by ipra_ring) (by ipra_ring) orig.andE₂)
  have rate := GaussianBoundedConstantProductRate.original_rate inv constantF R c a b (E*E) D hd coeff
    (GaussianNamedPositiveReciprocalFrozen.original_rate f k x E T hs.andE₂.andE₂)
  have s₁ := GaussianBoundedConstantProductName.ordinary_product_identity constantF R c b
    (.andI (constant_regular b) coeff)
  have s₂ := GaussianGammaWeierstrassApproximant.constant_product_cross (Γ := Γ) c b
  have e := GaussianEulerPowerScalingParameter.original_rescaled_value z B (numerator f k x) (denominator f k x)
    orig.andE₁ (decoded_domain f k x E T hs.andE₂.andE₂).andE₁.andE₁
  have s₃ := GaussianGammaWeierstrassApproximant.constant_data_cross _ _ e
  have moved : Γ ⊢[PRAAx] crossEquivalent P constantF d (frozenPoint f k z B x) :=
    cross_trans _ _ _ _ _ _ s₁ (cross_trans _ _ _ _ _ _ s₂ s₃)
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hd rate
    (cross_refl _ _ (regular f z R B A x E T hs)) (cross_symm _ _ _ _ moved)

theorem actual_named_rescaled_parameter_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source f (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        independentRate (nameF f) constantF (data (var 1) (var 2) (var 3) (var 5) (var 6))
          (frozenPoint f (var 0) (var 1) (var 3) (var 5)) (var 2*(var 6*var 6)) (unit (var 0))) :=
  closeUniv 8 (.impI (original_frozen_rate f _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedPowerScalingParameterFrozen
