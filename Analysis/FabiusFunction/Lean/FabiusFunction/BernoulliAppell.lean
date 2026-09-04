import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The Appell translation formula for Bernoulli polynomials

`β_n(x + y) = ∑_{k ≤ n} C(n,k) β_k(x) y^{n-k}`.

Mathlib provides `β_n' = n β_{n-1}` (`Polynomial.derivative_bernoulli`); iterating
it gives `β_n^{(k)} = n^{\underline k} β_{n-k}`, hence the Hasse derivatives
`β_n^{[k]} = C(n,k) β_{n-k}`, and the Taylor expansion
`β_n(x + y) = ∑_k β_n^{[k]}(x) y^k` is the translation formula.

## Main results

* `iterate_derivative_bernoulli`, `hasseDeriv_bernoulli`, `natDegree_bernoulli_le`.
* `bernoulli_eval_add`: the translation formula.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-- `β_n^{(k)} = n^{\underline k} β_{n-k}`. -/
theorem iterate_derivative_bernoulli (n k : ℕ) :
    (derivative : ℚ[X] → ℚ[X])^[k] (Polynomial.bernoulli n) =
      (n.descFactorial k : ℚ[X]) * Polynomial.bernoulli (n - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_mul, derivative_natCast, zero_mul, zero_add,
      Polynomial.derivative_bernoulli, Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

/-- The Hasse derivatives of the Bernoulli polynomials: `β_n^{[k]} = C(n,k) β_{n-k}`. -/
theorem hasseDeriv_bernoulli (n k : ℕ) :
    hasseDeriv k (Polynomial.bernoulli n) = (n.choose k : ℚ[X]) * Polynomial.bernoulli (n - k) := by
  have h := congrFun (factorial_smul_hasseDeriv (R := ℚ) (k := k)) (Polynomial.bernoulli n)
  rw [LinearMap.smul_apply, iterate_derivative_bernoulli,
    Nat.descFactorial_eq_factorial_mul_choose, nsmul_eq_mul] at h
  have hk : ((k.factorial : ℕ) : ℚ[X]) ≠ 0 := by
    rw [ne_eq, Nat.cast_eq_zero]
    exact Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hk
  rw [h]
  push_cast
  ring

/-- `deg β_n ≤ n`. -/
theorem natDegree_bernoulli_le (n : ℕ) : (Polynomial.bernoulli n).natDegree ≤ n := by
  rw [Polynomial.bernoulli_def]
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- **The Appell translation formula:**
`β_n(x + y) = ∑_{k ≤ n} C(n,k) β_k(x) y^{n-k}`. -/
theorem bernoulli_eval_add (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * y ^ (n - k) := by
  rw [add_comm, ← taylor_eval x (Polynomial.bernoulli n) y,
    eval_eq_sum_range' (n := n + 1)
      (by rw [natDegree_taylor]; exact Nat.lt_succ_of_le (natDegree_bernoulli_le n)),
    ← Finset.sum_range_reflect
      (fun k => (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * y ^ (n - k)) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [taylor_coeff, hasseDeriv_bernoulli, eval_mul, eval_natCast, Nat.add_sub_cancel,
    Nat.sub_sub_self hkn, Nat.choose_symm hkn]

end Fabius
