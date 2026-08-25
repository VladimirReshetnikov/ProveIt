import FabiusFunction.FabiusSharpConstant
import FabiusFunction.LaplaceMomentBounds

/-!
# Unconditional sharp dyadic formula in cumulant form

This module combines the exact Euler--Stieltjes constant with the unconditional endpoint/Laplace
comparison.  The result already has the final `O(1/n)` precision; its remaining second-order
cumulant is kept exact here.  A subsequent phase module rewrites that term as the displacement of
the periodic correction to its lower-Lambert saddle coordinate.  The asymptotic is also exposed
effectively: for `n ≥ 224043`, the logarithmic error is at most
`2512945 / (12n)`.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- Sharp dyadic main term with the evaluated constant and the exact endpoint cumulant. -/
noncomputable def dyadicSharpExplicitCumulantMain
    (F : BoundedFabius) (n : ℕ) : ℝ :=
  dyadicSharpElementaryMain n + fabiusSharpAsymptoticConstant +
    negativeLaplacePsi (Real.logb 2 n) - dyadicEndpointSecondOrder F n

/-- The explicit-constant and mean-normalized cumulant main terms agree exactly. -/
theorem dyadicSharpExplicitCumulantMain_eq
    (F : BoundedFabius) (n : ℕ) :
    dyadicSharpExplicitCumulantMain F n = dyadicSharpCumulantMain F n := by
  unfold dyadicSharpExplicitCumulantMain dyadicSharpCumulantMain
  rw [← negativeLaplacePeriodicMean_sub_log_two_pi_half]

/-- Effective version of
`log_fabius_dyadic_sub_explicitCumulantMain_isBigO`, with the evaluated
constant: the error is at most `2512945 / (12n)` for `n ≥ 224043`. -/
theorem abs_log_fabius_dyadic_sub_explicitCumulantMain_le
    (F : BoundedFabius) (hF : IsFabius F)
    {n : ℕ} (hn : 224043 ≤ n) :
    |Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpExplicitCumulantMain F n| ≤
      2512945 / (12 * (n : ℝ)) := by
  simpa only [dyadicSharpExplicitCumulantMain_eq] using
    abs_log_fabius_dyadic_sub_cumulantMain_le_unconditional F hF hn

/-- Unconditional sharp dyadic asymptotic, with the exact second endpoint cumulant retained. -/
theorem log_fabius_dyadic_sub_explicitCumulantMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ =>
      Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpExplicitCumulantMain F n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  simpa only [dyadicSharpExplicitCumulantMain_eq] using
    log_fabius_dyadic_sub_cumulantMain_isBigO_unconditional F hF

end Fabius
