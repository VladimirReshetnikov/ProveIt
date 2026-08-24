import FabiusFunction.NegativeLaplaceVerticalLog
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# All-order smoothness of the vertical negative-Laplace logarithm

The branch-safe logarithm on a positive vertical line was originally used
only through four derivatives.  An all-orders saddle expansion needs every
derivative.  The underlying transform curve is smooth to every order and
never vanishes, so its logarithmic derivative has the same regularity; the
fundamental theorem of calculus then promotes the normalized logarithm too.
-/

set_option autoImplicit false

namespace Fabius

theorem contDiff_negativeLaplaceVerticalLogDerivative_infty
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (negativeLaplaceVerticalLogDerivative F r) := by
  unfold negativeLaplaceVerticalLogDerivative
  have hcurve := contDiff_negativeLaplaceVerticalCurve F hF r
  have hcurveSmooth : ContDiff ℝ (↑(⊤ : ℕ∞))
      (negativeLaplaceVerticalCurve F r) := hcurve.of_le (by simp)
  have hcurveDeriv : ContDiff ℝ (↑(⊤ : ℕ∞))
      (deriv (negativeLaplaceVerticalCurve F r)) :=
    (contDiff_infty_iff_deriv.mp hcurveSmooth).2
  exact hcurveDeriv.mul
    (hcurveSmooth.inv (negativeLaplaceVerticalCurve_ne_zero F hF hr))

theorem contDiff_negativeLaplaceVerticalLog_infty
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (negativeLaplaceVerticalLog F r) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun theta =>
    (negativeLaplaceVerticalLog_hasDerivAt F hF hr theta).differentiableAt, ?_⟩
  have hderiv : deriv (negativeLaplaceVerticalLog F r) =
      negativeLaplaceVerticalLogDerivative F r := by
    funext theta
    exact (negativeLaplaceVerticalLog_hasDerivAt F hF hr theta).deriv
  rw [hderiv]
  exact contDiff_negativeLaplaceVerticalLogDerivative_infty F hF hr

theorem contDiff_iteratedDeriv_negativeLaplaceVerticalLog_infty
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (iteratedDeriv k (negativeLaplaceVerticalLog F r)) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv k
    (contDiff_negativeLaplaceVerticalLog_infty F hF hr)

theorem continuous_iteratedDeriv_negativeLaplaceVerticalLog
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Continuous (iteratedDeriv k (negativeLaplaceVerticalLog F r)) :=
  (contDiff_iteratedDeriv_negativeLaplaceVerticalLog_infty F hF hr k).continuous

end Fabius
