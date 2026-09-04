import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Faulhaber's formula with an offset

`∑_{j < N} (x + j)^p = (β_{p+1}(x + N) - β_{p+1}(x)) / (p+1)`,

by telescoping the difference identity `β_{p+1}(y + 1) - β_{p+1}(y) = (p+1) y^p`
(Mathlib's `Polynomial.bernoulli_eval_one_add`).

## Main results

* `sum_range_add_pow_eq_bernoulli_sub`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-- **Faulhaber with an offset:**
`∑_{j < N} (x + j)^p = (β_{p+1}(x + N) - β_{p+1}(x)) / (p + 1)`. -/
theorem sum_range_add_pow_eq_bernoulli_sub (p N : ℕ) (x : ℚ) :
    ∑ j ∈ Finset.range N, (x + j) ^ p =
      ((Polynomial.bernoulli (p + 1)).eval (x + N) - (Polynomial.bernoulli (p + 1)).eval x) /
        (p + 1) := by
  have hp : ((p : ℚ) + 1) ≠ 0 := by positivity
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h := Polynomial.bernoulli_eval_one_add (p + 1) (x + N)
    rw [Nat.add_sub_cancel, show (1 : ℚ) + (x + N) = x + ((N + 1 : ℕ) : ℚ) by push_cast; ring] at h
    rw [h, eq_div_iff hp, add_mul, div_mul_cancel₀ _ hp]
    push_cast
    ring

end Fabius
