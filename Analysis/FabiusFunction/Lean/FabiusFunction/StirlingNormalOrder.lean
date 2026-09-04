import FabiusFunction.StirlingBasisChange
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Stirling normal-ordering identities

For the Euler operator `θ = x D` on polynomials,

`(x D)^n = ∑_{k ≤ n} S(n,k) x^k D^k` and `x^n D^n = ∑_{k ≤ n} s(n,k) (x D)^k`.

The first identity is proved by induction on `n` from
`x D (x^k D^k p) = k x^k D^k p + x^{k+1} D^{k+1} p` and the recurrence
`S(n+1,k) = k S(n,k) + S(n,k-1)`; the second is its Stirling inversion.

## Main results

* `xkDk`, `X_mul_derivative_xkDk`.
* `iterate_X_mul_derivative`: `(x D)^n p = ∑_k S(n,k) x^k D^k p`.
* `xkDk_eq_sum_signedStirlingFirst`: `x^n D^n p = ∑_k s(n,k) (x D)^k p`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

variable {R : Type*} [CommRing R]

/-- The operator `x^k D^k` applied to `p`. -/
noncomputable def xkDk (p : R[X]) (k : ℕ) : R[X] :=
  X ^ k * (derivative : R[X] → R[X])^[k] p

/-- `x D (x^k D^k p) = k x^k D^k p + x^{k+1} D^{k+1} p`. -/
theorem X_mul_derivative_xkDk (p : R[X]) (k : ℕ) :
    X * derivative (xkDk p k) = (k : R[X]) * xkDk p k + xkDk p (k + 1) := by
  cases k with
  | zero => simp [xkDk]
  | succ k =>
    rw [xkDk, xkDk, derivative_mul, derivative_X_pow,
      Function.iterate_succ_apply' derivative (k + 1) p, Nat.add_sub_cancel, C_eq_natCast]
    ring

/-- **Normal ordering of `(x D)^n`:** `(x D)^n p = ∑_{k ≤ n} S(n,k) x^k D^k p`. -/
theorem iterate_X_mul_derivative (p : R[X]) (n : ℕ) :
    (fun q : R[X] => X * derivative q)^[n] p =
      ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : R[X]) * xkDk p k := by
  induction n with
  | zero => simp [xkDk]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    show X * derivative (∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : R[X]) * xkDk p k)
      = _
    rw [derivative_sum, Finset.mul_sum]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        X * derivative ((Nat.stirlingSecond n k : R[X]) * xkDk p k)
          = (Nat.stirlingSecond n k : R[X]) * ((k : R[X]) * xkDk p k)
            + (Nat.stirlingSecond n k : R[X]) * xkDk p (k + 1) := by
      intro k _
      rw [derivative_mul, derivative_natCast, zero_mul, zero_add, mul_left_comm,
        X_mul_derivative_xkDk, mul_add]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_range_succ' (fun k => (Nat.stirlingSecond (n + 1) k : R[X]) * xkDk p k) (n + 1),
      Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, add_zero]
    have hsplit : ∑ k ∈ Finset.range (n + 1),
        (Nat.stirlingSecond (n + 1) (k + 1) : R[X]) * xkDk p (k + 1)
        = ∑ k ∈ Finset.range (n + 1),
            ((k + 1 : ℕ) : R[X]) * (Nat.stirlingSecond n (k + 1) : R[X]) * xkDk p (k + 1)
          + ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : R[X]) * xkDk p (k + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.stirlingSecond_succ_succ]
      push_cast
      ring
    have hshift : ∑ k ∈ Finset.range (n + 1),
        ((k + 1 : ℕ) : R[X]) * (Nat.stirlingSecond n (k + 1) : R[X]) * xkDk p (k + 1)
        = ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : R[X]) * ((k : R[X]) * xkDk p k) := by
      rw [Finset.sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n),
        Nat.cast_zero, mul_zero, zero_mul, add_zero,
        Finset.sum_range_succ' (fun k => (Nat.stirlingSecond n k : R[X]) * ((k : R[X]) * xkDk p k)) n,
        Nat.cast_zero, zero_mul, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [hsplit, hshift]

/-- **Normal ordering of `x^n D^n`:** `x^n D^n p = ∑_{k ≤ n} s(n,k) (x D)^k p`, the
Stirling inversion of `iterate_X_mul_derivative`. -/
theorem xkDk_eq_sum_signedStirlingFirst (p : R[X]) (n : ℕ) :
    xkDk p n = ∑ k ∈ Finset.range (n + 1),
      (signedStirlingFirst n k : R[X]) * (fun q : R[X] => X * derivative q)^[k] p := by
  have h := stirling_inversion (fun k => xkDk p k) (fun n => (fun q : R[X] => X * derivative q)^[n] p)
    (fun n => by
      rw [iterate_X_mul_derivative]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zsmul_eq_mul, Int.cast_natCast]) n
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul]

end Fabius
