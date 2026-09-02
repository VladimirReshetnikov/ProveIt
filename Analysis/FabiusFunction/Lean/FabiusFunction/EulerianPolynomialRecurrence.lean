import FabiusFunction.EulerianNumbers
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The Eulerian recurrence in polynomial form

The source states the Eulerian insertion recurrence and then its polynomial equivalent

`A_n(t) = (1 + (n-1) t) A_{n-1}(t) + t(1-t) A_{n-1}'(t)`   (`eulerianPolynomial_succ`),

over any commutative ring.  Only the numerical form was in the corpus.

The proof is a coefficient computation, and two small facts make it short.  First, every
coefficient of `A_n` is the corresponding Eulerian number with no range condition
(`coeff_eulerianPolynomial`), because the numbers above the diagonal already vanish; that
removes the case split on `k ≤ n` that the `if` in the sum representation would otherwise
force.  Second, `X A'` has the uniform coefficient `k a_k` (`coeff_X_mul_derivative`), with no
truncated subtraction, so the derivative term needs no separate treatment at `k = 0`.

The only genuine subtlety is that the numerical recurrence carries `n - k` as a truncated
natural subtraction while the polynomial identity carries the ring difference `n - k`.  They
disagree exactly when `k > n`, where the Eulerian number they multiply is zero
(`natCast_sub_mul_eulerianNumber`).

## Main results

* `eulerianNumber_eq_zero_of_lt`, `coeff_eulerianPolynomial`.
* `coeff_X_mul_derivative`, `natCast_sub_mul_eulerianNumber`.
* `eulerianPolynomial_succ`.
-/

set_option autoImplicit false

open Polynomial

namespace Fabius

/-- `A(n,k) = 0` above the diagonal. -/
theorem eulerianNumber_eq_zero_of_lt {n k : ℕ} (h : n < k) : eulerianNumber n k = 0 := by
  cases n with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact eulerianNumber_zero_succ m
  | succ n => exact eulerianNumber_eq_zero_of_le (by omega) (by omega)

section Poly

variable (R : Type*) [CommRing R]

/-- **Every coefficient is an Eulerian number,** with no range condition. -/
theorem coeff_eulerianPolynomial (n k : ℕ) :
    (eulerianPolynomial R n).coeff k = (eulerianNumber n k : R) := by
  have hmon : ∀ j, ((eulerianNumber n j : ℕ) : R[X]) * X ^ j
      = monomial j ((eulerianNumber n j : ℕ) : R) := by
    intro j
    rw [← C_eq_natCast, C_mul_X_pow_eq_monomial]
  rw [eulerianPolynomial, Finset.sum_congr rfl fun j _ => hmon j, coeff_sum_monomial_range]
  rcases le_or_gt k n with h | h
  · rw [if_pos h]
  · rw [if_neg (by omega), eulerianNumber_eq_zero_of_lt h, Nat.cast_zero]

/-- `[t^k] (t p'(t)) = k [t^k] p(t)`, uniformly in `k`. -/
theorem coeff_X_mul_derivative (p : R[X]) (k : ℕ) :
    (X * derivative p).coeff k = (k : R) * p.coeff k := by
  cases k with
  | zero =>
    rw [mul_coeff_zero, coeff_X_zero, zero_mul, Nat.cast_zero, zero_mul]
  | succ j =>
    rw [Polynomial.coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- The truncated natural subtraction may be replaced by the ring difference, because the two
disagree only where the Eulerian number vanishes. -/
theorem natCast_sub_mul_eulerianNumber (n m : ℕ) :
    ((n - m : ℕ) : R) * (eulerianNumber n m : R) =
      ((n : R) - (m : R)) * (eulerianNumber n m : R) := by
  rcases le_or_gt m n with h | h
  · rw [Nat.cast_sub h]
  · rw [eulerianNumber_eq_zero_of_lt h, Nat.cast_zero, mul_zero, mul_zero]

/-- **The Eulerian recurrence in polynomial form:**
`A_{n+1}(t) = (1 + n t) A_n(t) + t(1-t) A_n'(t)`. -/
theorem eulerianPolynomial_succ (n : ℕ) :
    eulerianPolynomial R (n + 1) =
      (1 + C (n : R) * X) * eulerianPolynomial R n +
        X * (1 - X) * derivative (eulerianPolynomial R n) := by
  have hexp : (1 + C (n : R) * X) * eulerianPolynomial R n +
      X * (1 - X) * derivative (eulerianPolynomial R n)
      = eulerianPolynomial R n + C (n : R) * (X * eulerianPolynomial R n)
        + X * derivative (eulerianPolynomial R n)
        - X * (X * derivative (eulerianPolynomial R n)) := by ring
  rw [hexp]
  ext k
  rw [coeff_sub, coeff_add, coeff_add, coeff_C_mul, coeff_X_mul_derivative,
    coeff_eulerianPolynomial, coeff_eulerianPolynomial]
  cases k with
  | zero =>
    rw [mul_coeff_zero, coeff_X_zero, zero_mul, mul_coeff_zero, coeff_X_zero, zero_mul,
      eulerianNumber_succ_zero, eulerianNumber_zero_right, Nat.cast_zero, zero_mul]
    ring
  | succ m =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul, coeff_X_mul_derivative,
      coeff_eulerianPolynomial, eulerianNumber_succ_succ]
    push_cast
    rw [natCast_sub_mul_eulerianNumber]
    ring

end Poly

end Fabius
