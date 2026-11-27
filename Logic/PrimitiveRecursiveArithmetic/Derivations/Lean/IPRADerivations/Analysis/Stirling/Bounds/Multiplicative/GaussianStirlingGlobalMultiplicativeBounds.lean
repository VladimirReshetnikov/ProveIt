import IPRADerivations.Analysis.Stirling.Robbins.GaussianStirlingFactorialRobbinsExponential
import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrement

/-!
# Unconditional multiplicative Stirling bounds for positive rational arguments

The original fractional increment establishes the hypotheses of the
strict exponential and rational comparison theorems on the original
quotient names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGlobalMultiplicativeBounds

open_ipra
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianStirlingFactorialRobbinsExponential (capF capData lower_log_strict upper_log_strict rational_exponential_bounds)
open GaussianStirlingGammaFractionalIncrement (original_first_order original_rational_robbins)
open GaussianStirlingLogDuplication (exponential_regular)
open GaussianStirlingMultiplicative (quotientF quotientData multiplicative_formula)
open GaussianStirlingMultiplicativeAlgebra (remainder_regular)
open GaussianStirlingMultiplicativeBounds (remainder_real)
open GaussianStirlingMultiplicativeBoundsCaps (rational_interval cap_denominator conventional_le_factor)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_exponential_order strict_transport)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (upperValue lowerValue upper_den_positive lower_den_positive small_numeral_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def relativeUpper (a b : PTm n) : PTm n := fraction (num 6*a+b) (num 6*a)

theorem all_positive_caps (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] strictOrder constantF quotientF (fraction one one) (quotientData a b x) ⋏
      strictOrder quotientF capF (quotientData a b x) (capData (upperValue a b)) :=
  rational_exponential_bounds a b x hs (original_first_order a b x hs)

theorem relative_error (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] strictOrder constantF quotientF (fraction one one) (quotientData a b x) ⋏
      strictOrder quotientF constantF (quotientData a b x) (relativeUpper a b) := by
  have bounds := rational_interval a b x hs hba (original_first_order a b x hs)
  have k := positive_product _ _ (small_numeral_positive 5) hs.andE₁
  have hc := conventional_le_factor a b (num 6*a) hs hba k (cap_denominator a b hs hba).andE₁
  refine .andI bounds.andE₁.andE₁ (.andI bounds.andE₂ (.impI ?_))
  exact bounds.andE₁.andE₂.andE₂.wk.impE (order_trans _ _ _ _ _ _ hc.wk Prf.hyp0)

private theorem fraction_real (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples constantF (fraction a b) :=
  GaussianStirlingNames.constant_real _ (GaussianRationalHorner.ofGaussian_canonical _ _ hb)
    (GaussianStirlingNames.fraction_axis a b hb)

theorem robbins_caps (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] strictOrder capF quotientF (capData (lowerValue a b)) (quotientData a b x) ⋏
      strictOrder quotientF capF (quotientData a b x) (capData (upperValue a b)) := by
  have obs := original_rational_robbins a b x hs hba
  have hr := remainder_regular a b x hs
  have ra := remainder_real a b x hs
  have e := multiplicative_formula a b x hs
  have lo := strict_exponential_order _ _ _ _ (constant_regular _) hr
    (fraction_real _ _ (lower_den_positive a b hs.andE₁)) ra (lower_log_strict a b x hs hba obs.andE₁)
  have hi := strict_exponential_order _ _ _ _ hr (constant_regular _) ra
    (fraction_real _ _ (upper_den_positive a hs.andE₁)) (upper_log_strict a b x hs obs.andE₂)
  have cl := exponential_regular constantF (lowerValue a b) (constant_regular (Γ := Γ) _)
  have cu := exponential_regular constantF (upperValue a b) (constant_regular (Γ := Γ) _)
  exact .andI (strict_transport _ _ _ _ _ _ _ _ (cross_refl _ _ cl) e lo)
    (strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ e) (cross_refl _ _ cu) hi)

theorem actual_rational_Stirling_strict_exponential_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶
      (strictOrder constantF quotientF (fraction one one) (quotientData (var 0) (var 1) (var 2)) ⋏
        strictOrder quotientF capF (quotientData (var 0) (var 1) (var 2)) (capData (upperValue (var 0) (var 1))))) :=
  closeUniv 3 (.impI (all_positive_caps _ _ _ Prf.hyp0))

theorem actual_rational_Stirling_strict_relative_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source (var 0) (var 1) ⋏ le (var 1) (var 0)) ⟶
      (strictOrder constantF quotientF (fraction one one) (quotientData (var 0) (var 1) (var 2)) ⋏
        strictOrder quotientF constantF (quotientData (var 0) (var 1) (var 2)) (relativeUpper (var 0) (var 1)))) :=
  closeUniv 3 (.impI (relative_error _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_rational_Robbins_strict_exponential_caps_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source (var 0) (var 1) ⋏ le (var 1) (var 0)) ⟶
      (strictOrder capF quotientF (capData (lowerValue (var 0) (var 1))) (quotientData (var 0) (var 1) (var 2)) ⋏
        strictOrder quotientF capF (quotientData (var 0) (var 1) (var 2)) (capData (upperValue (var 0) (var 1))))) :=
  closeUniv 3 (.impI (robbins_caps _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingGlobalMultiplicativeBounds
