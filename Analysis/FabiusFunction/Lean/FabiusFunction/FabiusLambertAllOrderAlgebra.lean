import FabiusFunction.FabiusLambertHigherExpansion

/-!
# All-order algebra for the lower-Lambert phase

Writing `ell = log t`, the lower-Lambert solution of
`lambda - log(lambda) / log 2 = t` has formal displacement
`lambda - t = sum_n a_n(ell) t^(-n)`.  This module defines the
coefficient polynomials `a_n` by their exact recursive algebra, exposes
scalar evaluation formulas, and connects the first nontrivial truncation to
the already proved quantitative Lambert expansion.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Polynomial Filter Asymptotics

namespace Fabius

private noncomputable def dyadicLambertDisplacementPolynomialStep
    (n : ℕ) (p : (m : ℕ) → m < n → Polynomial ℝ) : Polynomial ℝ :=
  match n with
  | 0 => C (Real.log 2)⁻¹ * X
  | q + 1 =>
      C (Real.log 2)⁻¹ * p q (Nat.lt_succ_self q) -
        C ((q + 1 : ℝ)⁻¹) *
          ∑ j : Fin q,
            C ((q - j : ℕ) : ℝ) *
                p j (lt_trans j.isLt (Nat.lt_succ_self q)) *
              p (q - j) (Nat.lt_succ_of_le (Nat.sub_le q j))

/-- Polynomial coefficients of the all-order lower-Lambert displacement.
If `ell = log t`, the exact phase has the formal expansion
`lambda(t) = t + sum_n a_n(ell) t^(-n)`. -/
noncomputable def dyadicLambertDisplacementPolynomial (n : ℕ) : Polynomial ℝ :=
  Nat.strongRec dyadicLambertDisplacementPolynomialStep n

@[simp] theorem dyadicLambertDisplacementPolynomial_zero :
    dyadicLambertDisplacementPolynomial 0 = C (Real.log 2)⁻¹ * X := by
  rw [dyadicLambertDisplacementPolynomial, Nat.strongRec_eq]
  rfl

/-- The defining recurrence, unfolded from the strong recursion:
`a_(n+1) = (log 2)⁻¹ * a_n - (n + 1)⁻¹ * ∑ j : Fin n, (n - j) * a_j * a_(n-j)`,
where `n - j` is truncated natural subtraction.  Used by
`dyadicLambertDisplacementPolynomial_one` and `_two` in this file and by
`dyadicLambert_logCoeff_succ` in `FabiusFunction.FabiusLambertFormalLog`. -/
theorem dyadicLambertDisplacementPolynomial_succ (n : ℕ) :
    dyadicLambertDisplacementPolynomial (n + 1) =
      C (Real.log 2)⁻¹ * dyadicLambertDisplacementPolynomial n -
        C ((n + 1 : ℝ)⁻¹) *
          ∑ j : Fin n,
            C ((n - j : ℕ) : ℝ) *
                dyadicLambertDisplacementPolynomial j *
              dyadicLambertDisplacementPolynomial (n - j) := by
  rw [dyadicLambertDisplacementPolynomial, Nat.strongRec_eq]
  rfl

/-- Scalar evaluation of the formal displacement polynomial. -/
noncomputable def dyadicLambertDisplacementCoefficient
    (n : ℕ) (ell : ℝ) : ℝ :=
  (dyadicLambertDisplacementPolynomial n).eval ell

@[simp] theorem dyadicLambertDisplacementCoefficient_zero (ell : ℝ) :
    dyadicLambertDisplacementCoefficient 0 ell = ell / Real.log 2 := by
  rw [dyadicLambertDisplacementCoefficient,
    dyadicLambertDisplacementPolynomial_zero]
  simp only [eval_mul, eval_C, eval_X]
  ring

/-- Scalar form of the recurrence at a point `ell`: the value of `a_(n+1)` is
`a_n ell / log 2` minus `(n + 1)⁻¹` times the sum over `j : Fin n` of
`(n - j) * a_j ell * a_(n-j) ell`, with `n - j` truncated natural
subtraction. -/
theorem dyadicLambertDisplacementCoefficient_succ (n : ℕ) (ell : ℝ) :
    dyadicLambertDisplacementCoefficient (n + 1) ell =
      dyadicLambertDisplacementCoefficient n ell / Real.log 2 -
        (n + 1 : ℝ)⁻¹ *
          ∑ j : Fin n, (n - j : ℕ) *
            dyadicLambertDisplacementCoefficient j ell *
              dyadicLambertDisplacementCoefficient (n - j) ell := by
  simp only [dyadicLambertDisplacementCoefficient,
    dyadicLambertDisplacementPolynomial_succ, eval_sub, eval_mul,
    eval_C, eval_finsetSum]
  ring

/-- Closed form of the first displacement polynomial:
`a₁ = (log 2)⁻¹ ^ 2 * X`. -/
theorem dyadicLambertDisplacementPolynomial_one :
    dyadicLambertDisplacementPolynomial 1 =
      C ((Real.log 2)⁻¹ ^ 2) * X := by
  calc
    dyadicLambertDisplacementPolynomial 1 =
        C (Real.log 2)⁻¹ * dyadicLambertDisplacementPolynomial 0 -
          C ((0 + 1 : ℝ)⁻¹) * ∑ _j : Fin 0, 0 := by
      simpa using dyadicLambertDisplacementPolynomial_succ 0
    _ = C ((Real.log 2)⁻¹ ^ 2) * X := by
      rw [dyadicLambertDisplacementPolynomial_zero]
      simp only [Finset.univ_eq_empty, sum_empty, mul_zero, sub_zero]
      apply Polynomial.funext
      intro z
      simp only [eval_mul, eval_C, eval_X]
      ring

/-- Closed form of the second displacement polynomial:
`a₂ = (log 2)⁻¹ ^ 3 * (X - X ^ 2 / 2)`. -/
theorem dyadicLambertDisplacementPolynomial_two :
    dyadicLambertDisplacementPolynomial 2 =
      C ((Real.log 2)⁻¹ ^ 3) *
        (X - C (1 / 2 : ℝ) * X ^ 2) := by
  calc
    dyadicLambertDisplacementPolynomial 2 =
        C (Real.log 2)⁻¹ * dyadicLambertDisplacementPolynomial 1 -
          C ((1 + 1 : ℝ)⁻¹) *
            ∑ j : Fin 1,
              C ((1 - j : ℕ) : ℝ) *
                  dyadicLambertDisplacementPolynomial j *
                dyadicLambertDisplacementPolynomial (1 - j) := by
      simpa using dyadicLambertDisplacementPolynomial_succ 1
    _ = C ((Real.log 2)⁻¹ ^ 3) *
        (X - C (1 / 2 : ℝ) * X ^ 2) := by
      simp only [Fin.sum_univ_succ, Fin.val_zero, Nat.sub_zero,
        dyadicLambertDisplacementPolynomial_zero]
      rw [dyadicLambertDisplacementPolynomial_one]
      norm_num
      apply Polynomial.funext
      intro z
      simp only [eval_sub, eval_mul, eval_C, eval_X, eval_pow]
      ring

@[simp] theorem dyadicLambertDisplacementCoefficient_one (ell : ℝ) :
    dyadicLambertDisplacementCoefficient 1 ell =
      ell / (Real.log 2) ^ 2 := by
  rw [dyadicLambertDisplacementCoefficient,
    dyadicLambertDisplacementPolynomial_one]
  simp only [eval_mul, eval_C, eval_X]
  ring

@[simp] theorem dyadicLambertDisplacementCoefficient_two (ell : ℝ) :
    dyadicLambertDisplacementCoefficient 2 ell =
      (ell - ell ^ 2 / 2) / (Real.log 2) ^ 3 := by
  rw [dyadicLambertDisplacementCoefficient,
    dyadicLambertDisplacementPolynomial_two]
  simp only [eval_mul, eval_C, eval_sub, eval_X, eval_pow]
  ring

/-- The first `N+1` terms of the elementary lower-Lambert expansion. -/
noncomputable def dyadicLambertPhaseApproximation (N : ℕ) (t : ℝ) : ℝ :=
  t + ∑ n ∈ range (N + 1),
    dyadicLambertDisplacementCoefficient n (Real.log t) / t ^ n

/-- Error after truncating the elementary lower-Lambert expansion. -/
noncomputable def dyadicLambertAllOrderRemainder (N : ℕ) (t : ℝ) : ℝ :=
  dyadicLambertPhase t - dyadicLambertPhaseApproximation N t

/-- Closed form of the order-two truncation:
`t + log t / log 2 + log t / (log 2) ^ 2 / t +
(log t - (log t) ^ 2 / 2) / (log 2) ^ 3 / t ^ 2`.  No positivity hypothesis
on `t` is imposed. -/
theorem dyadicLambertPhaseApproximation_two (t : ℝ) :
    dyadicLambertPhaseApproximation 2 t =
      t + Real.log t / Real.log 2 +
        Real.log t / (Real.log 2) ^ 2 / t +
          (Real.log t - Real.log t ^ 2 / 2) /
            (Real.log 2) ^ 3 / t ^ 2 := by
  unfold dyadicLambertPhaseApproximation
  rw [show 2 + 1 = 3 by omega]
  simp only [sum_range_succ, sum_range_zero, zero_add,
    dyadicLambertDisplacementCoefficient_zero,
    dyadicLambertDisplacementCoefficient_one,
    dyadicLambertDisplacementCoefficient_two]
  norm_num
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hL]
  ring

/-- The order-two all-order remainder coincides, as a function on `ℝ`, with
`dyadicLambertSecondRefinedRemainder` of
`FabiusFunction.FabiusLambertHigherExpansion`. -/
theorem dyadicLambertAllOrderRemainder_two :
    dyadicLambertAllOrderRemainder 2 =
      dyadicLambertSecondRefinedRemainder := by
  funext t
  rw [dyadicLambertAllOrderRemainder,
    dyadicLambertPhaseApproximation_two]
  unfold dyadicLambertSecondRefinedRemainder dyadicLambertRemainder
  ring

/-- The order-two truncation error of the elementary lower-Lambert expansion
is `O((t⁻¹) ^ 2)` along `atTop`. -/
theorem dyadicLambertAllOrderRemainder_two_isBigO :
    dyadicLambertAllOrderRemainder 2 =O[atTop]
      (fun t : ℝ => t⁻¹ ^ 2) := by
  rw [dyadicLambertAllOrderRemainder_two]
  exact dyadicLambertSecondRefinedRemainder_isBigO

end Fabius
