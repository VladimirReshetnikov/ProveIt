import FabiusFunction.StirlingBasisChange

/-!
# Shifted factorial evaluations of the Stirling basis change

From `x^{n+1} = ∑_k S(n+1,k) x^{\underline k}` and `x^{\underline{k+1}} = x (x-1)^{\underline k}`,
cancelling the factor `x` gives

`x^n = ∑_{k ≤ n} S(n+1, k+1) (x-1)^{\underline k}`,

and evaluating `x^n = ∑_k S(n,k) x^{\underline k}` at `x = n` gives
`n^n = ∑_k S(n,k) n^{\underline k}`.

## Main results

* `X_mul_cancel`: `X` is a non-zero-divisor in `R[X]`.
* `X_pow_eq_sum_stirlingSecond_succ_mul_descPochhammer_comp`, `pow_self_eq_sum_stirlingSecond_mul_descFactorial`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

section

variable {R : Type*} [CommRing R]

/-- `X` is a non-zero-divisor in `R[X]`, over any commutative ring. -/
theorem X_mul_cancel {p q : R[X]} (h : X * p = X * q) : p = q := by
  ext n
  have := congrArg (fun r : R[X] => r.coeff (n + 1)) h
  simpa only [coeff_X_mul] using this

/-- **Shifted power-to-falling-factorial expansion:**
`X^n = ∑_{k ≤ n} S(n+1, k+1) · (X-1)^{\underline k}` in `R[X]`. -/
theorem X_pow_eq_sum_stirlingSecond_succ_mul_descPochhammer_comp (n : ℕ) :
    (X : R[X]) ^ n = ∑ k ∈ Finset.range (n + 1),
      (Nat.stirlingSecond (n + 1) (k + 1) : R[X]) * (descPochhammer R k).comp (X - 1) := by
  have h := X_pow_eq_sum_stirlingSecond_mul_descPochhammer R (n + 1)
  rw [Finset.sum_range_succ', Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, add_zero,
    pow_succ'] at h
  apply X_mul_cancel
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [descPochhammer_succ_left]
  ring

end

/-- `n^n = ∑_{k ≤ n} S(n,k) · n^{\underline k}`. -/
theorem pow_self_eq_sum_stirlingSecond_mul_descFactorial (n : ℕ) :
    n ^ n = ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k * n.descFactorial k :=
  pow_eq_sum_stirlingSecond_mul_descFactorial n n

end Fabius
