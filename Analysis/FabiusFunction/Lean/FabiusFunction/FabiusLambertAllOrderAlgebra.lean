import FabiusFunction.FabiusLambertHigherExpansion
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# All-order algebra for the lower-Lambert phase

Writing `ell = log t`, the lower-Lambert solution of
`lambda - log(lambda) / log 2 = t` has formal displacement
`lambda - t = sum_n a_n(ell) t^(-n)`.  This module defines the
coefficient polynomials `a_n` by their exact recursive algebra, exposes
scalar evaluation formulas, and connects the first nontrivial truncation to
the already proved quantitative Lambert expansion.

The recursion also determines the top of every coefficient polynomial.  Their
natural degrees are `1, 1, 2, 3, ...`, or exactly `max n 1` at index `n`, and
the leading coefficient of `a_(n+1)` is
`(-1)^n * (n+1)^(-1) * (log 2)^(-(n+2))`.  For recurrence indices `n ≥ 1`,
only the `j = 0` convolution term reaches the new highest degree; the case
`a_1 = (log 2)^(-2) X` supplies the separate base step.
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

/-- The zeroth displacement polynomial is `(log 2)⁻¹ X`. -/
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

/-- The zeroth scalar displacement coefficient is `ell / log 2`. -/
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

/-- Proof helper for the exact degree formula: the recursive polynomial at
index `n` has natural degree at most `max n 1`.  In each convolution summand,
the two recursive indices add to `n`; the extra `1` accommodates `a₀`. -/
private lemma dyadicLambertDisplacementPolynomial_natDegree_le (n : ℕ) :
    (dyadicLambertDisplacementPolynomial n).natDegree ≤ max n 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [dyadicLambertDisplacementPolynomial_zero]
          simpa using
            (Polynomial.natDegree_C_mul_le (Real.log 2)⁻¹
              (X : Polynomial ℝ))
      | succ n =>
          rw [Nat.succ_eq_add_one,
            dyadicLambertDisplacementPolynomial_succ]
          refine (Polynomial.natDegree_sub_le _ _).trans ?_
          rw [max_le_iff]
          constructor
          · calc
              (C (Real.log 2)⁻¹ *
                    dyadicLambertDisplacementPolynomial n).natDegree ≤
                  (dyadicLambertDisplacementPolynomial n).natDegree :=
                Polynomial.natDegree_C_mul_le _ _
              _ ≤ max n 1 := ih n (by omega)
              _ ≤ max (n + 1) 1 :=
                max_le_max (Nat.le_succ n) le_rfl
          · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
            apply Polynomial.natDegree_sum_le_of_forall_le
            intro j _hj
            calc
              (C ((n - (j : ℕ) : ℕ) : ℝ) *
                    dyadicLambertDisplacementPolynomial j *
                  dyadicLambertDisplacementPolynomial (n - (j : ℕ))).natDegree ≤
                  (C ((n - (j : ℕ) : ℕ) : ℝ) *
                      dyadicLambertDisplacementPolynomial j).natDegree +
                    (dyadicLambertDisplacementPolynomial
                      (n - (j : ℕ))).natDegree :=
                Polynomial.natDegree_mul_le
              _ ≤ (dyadicLambertDisplacementPolynomial j).natDegree +
                    (dyadicLambertDisplacementPolynomial
                      (n - (j : ℕ))).natDegree := by
                exact Nat.add_le_add_right
                  (Polynomial.natDegree_C_mul_le _ _) _
              _ ≤ max (j : ℕ) 1 + max (n - (j : ℕ)) 1 :=
                Nat.add_le_add (ih j (by omega))
                  (ih (n - (j : ℕ)) (by omega))
              _ ≤ n + 1 := by
                by_cases hj0 : (j : ℕ) = 0
                · have hnpos : 0 < n := by omega
                  rw [hj0, Nat.sub_zero,
                    max_eq_right (by omega : 0 ≤ 1),
                    max_eq_left (by omega : 1 ≤ n)]
                  omega
                · have hjone : 1 ≤ (j : ℕ) :=
                    Nat.one_le_iff_ne_zero.mpr hj0
                  have hsubone : 1 ≤ n - (j : ℕ) := by omega
                  rw [max_eq_left hjone, max_eq_left hsubone]
                  omega
              _ ≤ max (n + 1) 1 := le_max_left _ _

/-- Proof helper for the leading term.  The base case is
`a₁ = (log 2)⁻² X`.  In the successor step, whose recurrence index is already
positive, the `j = 0` summand is the unique term of the new top degree. -/
private lemma dyadicLambertDisplacementPolynomial_coeff_succ (n : ℕ) :
    (dyadicLambertDisplacementPolynomial (n + 1)).coeff (n + 1) =
      (-1 : ℝ) ^ n * (n + 1 : ℝ)⁻¹ *
        (Real.log 2)⁻¹ ^ (n + 2) := by
  induction n with
  | zero =>
      rw [dyadicLambertDisplacementPolynomial_one]
      norm_num [Polynomial.coeff_C_mul]
  | succ n ih =>
      have hlinear :
          (dyadicLambertDisplacementPolynomial (n + 1)).coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          ((dyadicLambertDisplacementPolynomial_natDegree_le (n + 1)).trans_lt
            (by
              rw [max_eq_left (by omega : 1 ≤ n + 1)]
              omega))
      have hhead :
          (C ((n + 1 : ℕ) : ℝ) *
                dyadicLambertDisplacementPolynomial 0 *
              dyadicLambertDisplacementPolynomial (n + 1)).coeff (n + 2) =
            (n + 1 : ℝ) * (Real.log 2)⁻¹ *
              (dyadicLambertDisplacementPolynomial (n + 1)).coeff (n + 1) := by
        rw [mul_assoc, Polynomial.coeff_C_mul,
          show n + 2 = 1 + (n + 1) by omega,
          Polynomial.coeff_mul_add_eq_of_natDegree_le
            (by
              simpa using
                dyadicLambertDisplacementPolynomial_natDegree_le 0)
            (by
              simpa using
                dyadicLambertDisplacementPolynomial_natDegree_le (n + 1)),
          dyadicLambertDisplacementPolynomial_zero,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_one]
        ring
      have htail (j : Fin n) :
          (C (((n + 1) - (j.succ : ℕ) : ℕ) : ℝ) *
                dyadicLambertDisplacementPolynomial j.succ *
              dyadicLambertDisplacementPolynomial
                ((n + 1) - (j.succ : ℕ))).coeff (n + 2) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        calc
          (C (((n + 1) - (j.succ : ℕ) : ℕ) : ℝ) *
                dyadicLambertDisplacementPolynomial j.succ *
              dyadicLambertDisplacementPolynomial
                ((n + 1) - (j.succ : ℕ))).natDegree ≤
              (C (((n + 1) - (j.succ : ℕ) : ℕ) : ℝ) *
                  dyadicLambertDisplacementPolynomial j.succ).natDegree +
                (dyadicLambertDisplacementPolynomial
                  ((n + 1) - (j.succ : ℕ))).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ (dyadicLambertDisplacementPolynomial j.succ).natDegree +
                (dyadicLambertDisplacementPolynomial
                  ((n + 1) - (j.succ : ℕ))).natDegree := by
            exact Nat.add_le_add_right
              (Polynomial.natDegree_C_mul_le _ _) _
          _ ≤ max (j.succ : ℕ) 1 +
                max ((n + 1) - (j.succ : ℕ)) 1 :=
            Nat.add_le_add
              (dyadicLambertDisplacementPolynomial_natDegree_le j.succ)
              (dyadicLambertDisplacementPolynomial_natDegree_le
                ((n + 1) - (j.succ : ℕ)))
          _ < n + 2 := by
            have hjlt : (j.succ : ℕ) < n + 1 := j.succ.isLt
            have hjone : 1 ≤ (j.succ : ℕ) := by omega
            have hsubone : 1 ≤ (n + 1) - (j.succ : ℕ) := by omega
            rw [max_eq_left hjone, max_eq_left hsubone]
            omega
      rw [dyadicLambertDisplacementPolynomial_succ]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.finsetSum_coeff, Fin.sum_univ_succ,
        Fin.val_zero, Nat.sub_zero]
      rw [hlinear, hhead]
      simp_rw [htail]
      simp only [mul_zero, Finset.sum_const_zero, add_zero, zero_sub, ih]
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      rw [show (Real.log 2)⁻¹ ^ (n + 3) =
          (Real.log 2)⁻¹ ^ (n + 2) * (Real.log 2)⁻¹ by
        rw [show n + 3 = n + 2 + 1 by omega, pow_succ]]
      calc
        -((n + 2 : ℝ)⁻¹ *
            ((n + 1 : ℝ) * (Real.log 2)⁻¹ *
              ((-1 : ℝ) ^ n * (n + 1 : ℝ)⁻¹ *
                (Real.log 2)⁻¹ ^ (n + 2)))) =
            -(n + 2 : ℝ)⁻¹ *
              ((n + 1 : ℝ) * (n + 1 : ℝ)⁻¹) *
                ((-1 : ℝ) ^ n *
                  ((Real.log 2)⁻¹ ^ (n + 2) * (Real.log 2)⁻¹)) := by ring
        _ = (-1 : ℝ) ^ (n + 1) * (n + 2 : ℝ)⁻¹ *
              ((Real.log 2)⁻¹ ^ (n + 2) * (Real.log 2)⁻¹) := by
          rw [mul_inv_cancel₀ hn1, mul_one,
            show (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1 : ℝ) by
              rw [pow_succ]]
          ring

/-- The exact natural degree of the `n`th lower-Lambert displacement
polynomial is `max n 1`; equivalently, the degree sequence begins
`1, 1, 2, 3, ...`. -/
@[simp] theorem dyadicLambertDisplacementPolynomial_natDegree (n : ℕ) :
    (dyadicLambertDisplacementPolynomial n).natDegree = max n 1 := by
  cases n with
  | zero =>
      rw [dyadicLambertDisplacementPolynomial_zero]
      exact Polynomial.natDegree_C_mul_X _
        (inv_ne_zero (Real.log_pos (by norm_num)).ne')
  | succ n =>
      rw [show Nat.succ n = n + 1 by omega,
        max_eq_left (by omega : 1 ≤ n + 1)]
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · simpa using
          dyadicLambertDisplacementPolynomial_natDegree_le (n + 1)
      · have hlog : (Real.log 2)⁻¹ ≠ 0 :=
          inv_ne_zero (Real.log_pos (by norm_num)).ne'
        have hnat : (n + 1 : ℝ)⁻¹ ≠ 0 := by positivity
        rw [dyadicLambertDisplacementPolynomial_coeff_succ]
        exact mul_ne_zero
          (mul_ne_zero (pow_ne_zero _ (by norm_num)) hnat)
          (pow_ne_zero _ hlog)

/-- For every `n`, the leading coefficient of `a_(n+1)` is
`(-1)^n / ((n+1) * (log 2)^(n+2))`. -/
@[simp] theorem dyadicLambertDisplacementPolynomial_leadingCoeff_succ (n : ℕ) :
    (dyadicLambertDisplacementPolynomial (n + 1)).leadingCoeff =
      (-1 : ℝ) ^ n * (n + 1 : ℝ)⁻¹ *
        (Real.log 2)⁻¹ ^ (n + 2) := by
  rw [← Polynomial.coeff_natDegree,
    dyadicLambertDisplacementPolynomial_natDegree]
  simpa using dyadicLambertDisplacementPolynomial_coeff_succ n

/-- The first scalar displacement coefficient is `ell / (log 2)²`. -/
@[simp] theorem dyadicLambertDisplacementCoefficient_one (ell : ℝ) :
    dyadicLambertDisplacementCoefficient 1 ell =
      ell / (Real.log 2) ^ 2 := by
  rw [dyadicLambertDisplacementCoefficient,
    dyadicLambertDisplacementPolynomial_one]
  simp only [eval_mul, eval_C, eval_X]
  ring

/-- The second scalar displacement coefficient is
`(ell - ell² / 2) / (log 2)³`. -/
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
