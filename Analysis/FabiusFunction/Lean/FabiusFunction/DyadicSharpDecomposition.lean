import FabiusFunction.NegativeLaplaceDerivatives
import FabiusFunction.FabiusDyadicLogBounds
import FabiusFunction.PeriodicCorrection
import FabiusFunction.StirlingAsymptotics

/-!
# Exact decomposition behind the sharp dyadic asymptotic

This file performs the exact algebraic assembly of the dyadic formula before
any asymptotic estimates are inserted.  It separates

* the elementary quadratic/logarithmic main term;
* the exact periodic correction (or its centered normalization);
* the exponentially small product tail;
* the endpoint-moment versus Laplace-transform error; and
* the sharp Stirling remainder.

Thus the remaining analytic work is localized to the endpoint/Laplace error
and the evaluation/regularity of the periodic correction; no cancellation is
left hidden in the final proof.
-/

set_option autoImplicit false

namespace Fabius

/-- Difference between the exact endpoint moment and its negative-Laplace
approximation. -/
noncomputable def dyadicEndpointLaplaceLogError (n : ℕ) : ℝ :=
  Real.log (halfMoment n : ℝ) - negativeLaplaceLog n

/-- Exact remainder in the sharp logarithmic Stirling formula. -/
noncomputable def dyadicStirlingLogError (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) -
    ((n : ℝ) * Real.log n - n + Real.log n / 2 +
      Real.log (2 * Real.pi) / 2)

/-- The elementary part of the sharp dyadic logarithmic asymptotic, before
adding the constant, periodic correction, and the endpoint `1/n` term. -/
noncomputable def dyadicSharpElementaryMain (n : ℕ) : ℝ :=
  -Real.log 2 / 2 * (n : ℝ) ^ 2 -
    (n : ℝ) * Real.log n + (1 + Real.log 2 / 2) * n -
      Real.log n ^ 2 / (2 * Real.log 2)

/-- Exact decomposition from which the sharp dyadic asymptotic is assembled. -/
theorem log_fabius_dyadic_exact_sharp_decomposition
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) =
      dyadicSharpElementaryMain n +
        negativeLaplacePeriodicCorrection (Real.logb 2 n) -
        Real.log (2 * Real.pi) / 2 +
        negativeLaplaceTailError n + dyadicEndpointLaplaceLogError n -
        dyadicStirlingLogError n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [log_fabius_inverse_two_pow_eq F hF n,
    show Real.log (halfMoment n : ℝ) =
        negativeLaplaceLog n + dyadicEndpointLaplaceLogError n by
      unfold dyadicEndpointLaplaceLogError; ring,
    negativeLaplaceLog_exact_periodic_decomposition n hnreal,
    show Real.log (n.factorial : ℝ) =
        ((n : ℝ) * Real.log n - n + Real.log n / 2 +
          Real.log (2 * Real.pi) / 2) + dyadicStirlingLogError n by
      unfold dyadicStirlingLogError; ring,
    Nat.cast_choose_two ℝ]
  unfold dyadicSharpElementaryMain
  ring

/-- Centered-periodic version of the exact sharp decomposition. -/
theorem log_fabius_dyadic_exact_sharp_decomposition_centered
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) =
      dyadicSharpElementaryMain n +
        (negativeLaplacePeriodicMean - Real.log (2 * Real.pi) / 2) +
        negativeLaplacePsi (Real.logb 2 n) +
        negativeLaplaceTailError n + dyadicEndpointLaplaceLogError n -
        dyadicStirlingLogError n := by
  rw [log_fabius_dyadic_exact_sharp_decomposition F hF n hn]
  unfold negativeLaplacePsi
  ring

/-- The Stirling contribution to the exact decomposition is between zero and
`1/(12n)`. -/
theorem dyadicStirlingLogError_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ dyadicStirlingLogError n ∧
      dyadicStirlingLogError n ≤ (1 : ℝ) / (12 * n) := by
  exact log_factorial_sub_stirlingMain_bounds n hn

end Fabius
