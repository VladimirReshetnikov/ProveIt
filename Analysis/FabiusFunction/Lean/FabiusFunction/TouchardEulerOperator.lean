import FabiusFunction.BellStirling
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Touchard cumulants as iterates of the Euler operator

The transseries volume's `q2:def:touchard`: for `j ≥ 1`,

`T_j(r) = e^{-r} (r ∂_r)^j e^r = ∑_{k=1}^{j} S(j,k) r^k`,

with `q_j(r) = T_j(r) / (r (1+r)^{j/2})` the normalized form used at the
saddle.  The corpus already carries the right-hand side as a polynomial,
`touchardPolynomial`; what is added here is the *analytic* characterization,
which is what the saddle-point argument actually applies, and the bridge
between the two.

The whole content is one polynomial identity,

`T_{n+1} = X · (T_n + T_n')`,

the differential form of the Stirling recurrence
`S(n+1,k+1) = (k+1)S(n,k+1) + S(n,k)`.  Once it is available the analytic
statement is an induction whose step is the product rule: applying `r ∂_r` to
`e^r T_n(r)` produces `e^r · r (T_n + T_n')(r)`.

Nothing here needs `r > 0` or any positivity: `eulerOp` is defined by `deriv`,
the identity holds at every real `r`, and the normalized `q_j` is the only
place where a hypothesis appears, since it divides.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-! ### The polynomial recurrence -/

section Polynomials

variable (R : Type*) [CommRing R]

/-- `T_0 = 1`, the anchor of the induction: the empty Euler iterate leaves
`e^r` alone. -/
@[simp] theorem touchardPolynomial_zero : touchardPolynomial R 0 = 1 := by
  simp [touchardPolynomial]

/-- The coefficients of the Touchard polynomial are the Stirling numbers of the
second kind, at *every* index: beyond the degree both sides vanish. -/
theorem coeff_touchardPolynomial (n m : ℕ) :
    (touchardPolynomial R n).coeff m = (Nat.stirlingSecond n m : R) := by
  rw [touchardPolynomial, finsetSum_coeff]
  simp only [← C_eq_natCast, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (n + 1)) m fun k => (Nat.stirlingSecond n k : R)]
  by_cases hm : m ∈ Finset.range (n + 1)
  · rw [if_pos hm]
  · rw [if_neg hm, Nat.stirlingSecond_eq_zero_of_lt (by simpa using hm), Nat.cast_zero]

/-- **The differential form of the Stirling recurrence.**
`T_{n+1} = X · (T_n + T_n')`.  This is the identity that turns the Euler
operator into the Touchard family. -/
theorem touchardPolynomial_succ_eq_X_mul_add_derivative (n : ℕ) :
    touchardPolynomial R (n + 1) =
      X * (touchardPolynomial R n + derivative (touchardPolynomial R n)) := by
  ext m
  cases m with
  | zero =>
      rw [coeff_touchardPolynomial, Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_comm,
        coeff_mul_X_zero]
  | succ j =>
      rw [coeff_touchardPolynomial, coeff_X_mul, coeff_add, coeff_derivative,
        coeff_touchardPolynomial, coeff_touchardPolynomial, Nat.stirlingSecond_succ_succ]
      push_cast
      ring

end Polynomials

/-! ### The Euler operator -/

/-- The **Euler operator** `θ = r ∂_r`, acting on functions of a real
variable. -/
noncomputable def eulerOp (f : ℝ → ℝ) : ℝ → ℝ := fun r => r * deriv f r

/-- **`q2:eq:touchard`, analytic half.**  The `j`-th iterate of the Euler
operator applied to `e^r` is `e^r T_j(r)`.  Stated as an equality of
functions, since that is what the induction needs. -/
theorem iterate_eulerOp_exp (j : ℕ) :
    eulerOp^[j] Real.exp = fun r => Real.exp r * (touchardPolynomial ℝ j).eval r := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply' eulerOp j Real.exp, ih]
      funext r
      have hderiv : HasDerivAt (fun r => Real.exp r * (touchardPolynomial ℝ j).eval r)
          (Real.exp r * (touchardPolynomial ℝ j).eval r +
            Real.exp r * (derivative (touchardPolynomial ℝ j)).eval r) r :=
        (Real.hasDerivAt_exp r).mul ((touchardPolynomial ℝ j).hasDerivAt r)
      rw [eulerOp, hderiv.deriv, touchardPolynomial_succ_eq_X_mul_add_derivative,
        eval_mul, eval_X, eval_add]
      ring

/-- **`q2:eq:touchard`.**  Both halves at once: the Euler-operator description
and the Stirling sum are the same function of `r`. -/
theorem exp_neg_mul_iterate_eulerOp_exp (j : ℕ) (r : ℝ) :
    Real.exp (-r) * eulerOp^[j] Real.exp r =
      ∑ k ∈ Finset.range (j + 1), (Nat.stirlingSecond j k : ℝ) * r ^ k := by
  rw [congrFun (iterate_eulerOp_exp j) r, touchardPolynomial, eval_finsetSum]
  simp only [eval_mul, eval_pow, eval_X, eval_natCast]
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- The `k = 0` term of the Stirling sum vanishes for `j ≥ 1`, so the sum runs
from `1` as the volume writes it. -/
theorem eval_touchardPolynomial_succ_eq_sum_Icc (j : ℕ) (r : ℝ) :
    (touchardPolynomial ℝ (j + 1)).eval r =
      ∑ k ∈ Finset.Icc 1 (j + 1), (Nat.stirlingSecond (j + 1) k : ℝ) * r ^ k := by
  have hrange : Finset.range (j + 1 + 1) = insert 0 (Finset.Icc 1 (j + 1)) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [touchardPolynomial, eval_finsetSum]
  simp only [eval_mul, eval_pow, eval_X, eval_natCast]
  rw [hrange, Finset.sum_insert (by simp)]
  simp

/-! ### The normalized cumulants -/

/-- **`q2:eq:touchard`**, the normalized form `q_j(r) = T_j(r)/(r(1+r)^{j/2})`.
The half-integer power is a real power, so this is stated with `rpow`. -/
noncomputable def touchardQ (j : ℕ) (r : ℝ) : ℝ :=
  (touchardPolynomial ℝ j).eval r / (r * (1 + r) ^ ((j : ℝ) / 2))

/-- The defining relation of `q_j`, cleared of the denominator, wherever the
denominator is nonzero. -/
theorem touchardQ_mul (j : ℕ) {r : ℝ} (hr : r ≠ 0) (hr1 : 0 < 1 + r) :
    touchardQ j r * (r * (1 + r) ^ ((j : ℝ) / 2)) =
      Real.exp (-r) * eulerOp^[j] Real.exp r := by
  simp only [touchardQ]
  rw [div_mul_cancel₀ _ (mul_ne_zero hr (Real.rpow_pos_of_pos hr1 _).ne'),
    exp_neg_mul_iterate_eulerOp_exp, touchardPolynomial, eval_finsetSum]
  simp only [eval_mul, eval_pow, eval_X, eval_natCast]

/-- `T_j(1)` is the `j`-th Bell number, so `q_j(1) = B_j / 2^{j/2}`: the
normalization is exactly the one that makes the central value the Bell number
divided by the Gaussian factor. -/
theorem touchardQ_one (j : ℕ) : touchardQ j 1 = (Nat.bell j : ℝ) / 2 ^ ((j : ℝ) / 2) := by
  simp only [touchardQ]
  rw [touchardPolynomial_eval_one, one_mul]
  norm_num

end Fabius
