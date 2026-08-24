import FabiusFunction.PeriodicMean

/-!
# The constant in the sharp Fabius asymptotic

The mean of the logarithmic periodic correction combines with the Gaussian saddle prefactor.
This module names the resulting constant and records both its compact Gamma--zeta form and the
expanded Euler--Stieltjes expression printed in the sharp asymptotic.
-/

set_option autoImplicit false

namespace Fabius

/-- Constant term in the corrected sharp logarithmic Fabius asymptotic. -/
noncomputable def fabiusSharpAsymptoticConstant : ℝ :=
  gammaZetaConstant / Real.log 2 - 7 * Real.log 2 / 12 - Real.log Real.pi / 2

/-- Combining the exact periodic mean with the Gaussian normalization gives the sharp constant. -/
theorem negativeLaplacePeriodicMean_sub_log_two_pi_half :
    negativeLaplacePeriodicMean - Real.log (2 * Real.pi) / 2 =
      fabiusSharpAsymptoticConstant := by
  rw [negativeLaplacePeriodicMean_eq]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  unfold fabiusSharpAsymptoticConstant
  ring

/-- Expanded Euler--Stieltjes form of the sharp asymptotic constant. -/
theorem fabiusSharpAsymptoticConstant_eq :
    fabiusSharpAsymptoticConstant =
      (6 * Real.eulerMascheroniConstant ^ 2 + 12 * firstStieltjesConstant -
          Real.pi ^ 2) / (12 * Real.log 2) -
        7 * Real.log 2 / 12 - Real.log Real.pi / 2 := by
  unfold fabiusSharpAsymptoticConstant
  rw [gammaZetaConstant_eq_div_twelve]
  ring

end Fabius
