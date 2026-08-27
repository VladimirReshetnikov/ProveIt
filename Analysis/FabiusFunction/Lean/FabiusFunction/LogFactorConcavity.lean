import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Strict log-concavity of the canonical factors

The analytic heart of the audits' one-peak-per-lobe theorem
(`thm:one-peak` / strict log-concavity): each factor of the canonical
product `Φ(z) = ∏_m (1 - z²/m²)^{1+v₂(m)}` contributes

`d²/dx² log |1 - x²/m²| = -2·(m² + x²)/(m² - x²)² < 0`

between consecutive zeros, so the logarithm of every factor — and
hence, after termwise summation, of `|Φ|` itself — is strictly concave
on every interzero interval.  This file proves the per-factor formula
as exact `HasDerivAt` statements, with the strict negativity; the
termwise summation over the canonical product is the remaining
(uniform-convergence) step of the full theorem.

* `hasDerivAt_log_sq_sub_sq` — first derivative:
  `(log (a² - t²))' = -2x/(a² - x²)` at `x` (with `Real.log` acting as
  `log |·|`, the identity holds on both sides of each zero).
* `hasDerivAt_log_sq_sub_sq_deriv` — second derivative:
  `(-2t/(a² - t²))' = -2(a² + x²)/(a² - x²)²`.
* `log_factor_second_deriv_neg` — strict negativity for `a ≠ 0`.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-- First derivative of the log-factor:
`(log (a² - t²))' = -(2x)/(a² - x²)` wherever `a² - x² ≠ 0`. -/
theorem hasDerivAt_log_sq_sub_sq (a x : ℝ) (h : a ^ 2 - x ^ 2 ≠ 0) :
    HasDerivAt (fun t => Real.log (a ^ 2 - t ^ 2))
      (-(2 * x) / (a ^ 2 - x ^ 2)) x := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    have h1 := hasDerivAt_pow 2 x
    simpa using h1
  have hbase : HasDerivAt (fun t : ℝ => a ^ 2 - t ^ 2) (-(2 * x)) x :=
    hpow.const_sub (a ^ 2)
  exact hbase.log h

/-- Second derivative of the log-factor: the derivative of
`t ↦ -(2t)/(a² - t²)` at `x` is `-2(a² + x²)/(a² - x²)²`. -/
theorem hasDerivAt_log_sq_sub_sq_deriv (a x : ℝ) (h : a ^ 2 - x ^ 2 ≠ 0) :
    HasDerivAt (fun t => -(2 * t) / (a ^ 2 - t ^ 2))
      (-(2 * (a ^ 2 + x ^ 2)) / (a ^ 2 - x ^ 2) ^ 2) x := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    have h1 := hasDerivAt_pow 2 x
    simpa using h1
  have hnum : HasDerivAt (fun t : ℝ => -(2 * t)) (-2) x := by
    have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    exact h2.neg
  have hden : HasDerivAt (fun t : ℝ => a ^ 2 - t ^ 2) (-(2 * x)) x :=
    hpow.const_sub (a ^ 2)
  have hval : -(2 * (a ^ 2 + x ^ 2)) / (a ^ 2 - x ^ 2) ^ 2 =
      ((-2) * (a ^ 2 - x ^ 2) - -(2 * x) * (-(2 * x))) /
        (a ^ 2 - x ^ 2) ^ 2 := by
    ring
  rw [hval]
  exact hnum.div hden h

/-- **Strict concavity of each canonical factor**: for `a ≠ 0`, the
second derivative `-2(a² + x²)/(a² - x²)²` is strictly negative on
every interzero interval. -/
theorem log_factor_second_deriv_neg {a x : ℝ} (ha : a ≠ 0)
    (h : a ^ 2 - x ^ 2 ≠ 0) :
    -(2 * (a ^ 2 + x ^ 2)) / (a ^ 2 - x ^ 2) ^ 2 < 0 := by
  have hnum : 0 < 2 * (a ^ 2 + x ^ 2) := by positivity
  have hden : 0 < (a ^ 2 - x ^ 2) ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hden

end Fabius
