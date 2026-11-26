import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerPowerOrder
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerCompatibility

/-!
# The original Euler power square below time one

The actual original power is compared with the actual exponential of
the doubled coefficient (1/A-1) times the ordered harmonic logarithm.
Both genuine old-logarithm and harmonic queries are retained. This
gives the sharp lower-time signed geometry; rational-power endpoint
identification and integration of its majorant are separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerComparison

open_ipra
open GaussianEulerLowerPowerOrder (source inputF expF leftData rightData radius leftExpData rightExpData)
open GaussianEulerLowerPowerCoefficients (amplification)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianEulerUpperPowerCompatibility (doubleF doubleData squareF squareData
  double_sample_error_of_bound double_input_cross_of_bound original_power_square_of_input)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem old_source (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.source z B a b := .andI h.andE₁.andE₂.andE₁.andE₁ h.andE₂.andE₁

theorem double_sample_error (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 doubleF p (doubleData z B a b)) (ap2 inputF p (leftData z R B a b))
      (two*amplification R) (unit p) :=
  double_sample_error_of_bound p z B a b (amplification R) h.andE₂.andE₁
    (GaussianEulerLowerPowerCoefficients.real_multiplier_bound z R B A h.andE₁)

theorem double_input_cross (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    crossEquivalent doubleF inputF (doubleData z B a b) (leftData z R B a b) :=
  double_input_cross_of_bound z B a b (amplification R) (old_source z R B A a b h)
    (GaussianEulerLowerPowerCoefficients.real_multiplier_bound z R B A h.andE₁)

theorem original_power_square (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    crossEquivalent squareF expF (squareData z B a b) (leftExpData z R B a b) := by
  have hM := GaussianEulerLowerPowerCoefficients.real_multiplier_bound z R B A h.andE₁
  exact original_power_square_of_input z B a b (amplification R) (radius R b) (old_source z R B A a b h) hM
    (GaussianEulerLowerPowerOrder.product_input _ _ _ _ h.andE₂ hM)

/-- Actual original squared modulus has the sharp reference with the
literal coefficient (1/A-1), retaining independent observation errors. -/
theorem original_square_order (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    GaussianNamedPositiveExponentialOrder.realOrder squareF expF (squareData z B a b) (rightExpData R A a b) :=
  GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (original_power_square z R B A a b h)
    (GaussianNameEquivalence.cross_refl expF (rightExpData R A a b)
      (GaussianRadiusExponentialName.name_regular _ _ _
        (GaussianEulerLowerPowerOrder.product_input _ _ _ _ h.andE₂
          (GaussianEulerLowerPowerCoefficients.lower_multiplier_bound R A h.andE₁.andE₁))))
    (GaussianEulerLowerPowerOrder.ordered_exponentials z R B A a b h)

theorem original_squared_observations (p q z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper
      (GaussianRationalMetric.qnormSq (ap2 powerF (GaussianExponentialRealPart.squarePrecision powerF p (powerData z B a b)) (powerData z B a b)))
      (fstT (ap2 expF q (rightExpData R A a b))) (unit p+unit q) (unit p*unit q) :=
  RationalValueBounds.upper_congr (GaussianEulerUpperPowerCompatibility.actual_squared_norm_sample p z B a b) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedPositiveExponentialOrder.real_order_at _ _ _ _ p q (original_square_order z R B A a b h))

theorem original_lower_time_power_square_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      GaussianNamedPositiveExponentialOrder.realOrder squareF expF (squareData (var 0) (var 2) (var 4) (var 5))
        (rightExpData (var 1) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_square_order _ _ _ _ _ _ Prf.hyp0))
theorem original_lower_time_actual_squared_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      RationalValueBounds.upper
        (GaussianRationalMetric.qnormSq
          (ap2 powerF (GaussianExponentialRealPart.squarePrecision powerF (var 0) (powerData (var 2) (var 4) (var 6) (var 7)))
            (powerData (var 2) (var 4) (var 6) (var 7))))
        (fstT (ap2 expF (var 1) (rightExpData (var 3) (var 5) (var 6) (var 7))))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (original_squared_observations _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerComparison
