import FabiusFunction.TouchardShiftEGF
import FabiusFunction.TouchardCongruence
import FabiusFunction.BellStirling

/-!
# The polynomial Touchard congruence

`T_{n+p}(X) = T_{n+1}(X) + X^p T_n(X)` in `(ZMod p)[X]` for a prime `p`.

Spivey's identity for Touchard polynomials (`spivey_touchard`) holds in `ℚ[X]`;
since all its terms have integer coefficients it holds in `ℤ[X]`, hence in `R[X]`
for every commutative ring `R`.  Reading it in `(ZMod p)[X]` with `m = p`, the
Stirling numbers `S(p,j)` with `1 < j < p` vanish, the term `j = 1` is the Touchard
recurrence `X ∑_k C(n,k) T_k = T_{n+1}`, and in the term `j = p` only `k = n`
survives because `p^{n-k} = 0` for `k < n`.

## Main results

* `bell_complete_X_eq_touchardPolynomial`, `touchardPolynomial_add_eq_rat`,
  `touchardPolynomial_add_eq_int`, `touchardPolynomial_add_eq` (Spivey's identity for
  Touchard polynomials over any commutative ring).
* `touchardPolynomial_add_prime`: the polynomial Touchard congruence.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-- `T_n` is the complete Bell polynomial at constant weights `X`. -/
theorem bell_complete_X_eq_touchardPolynomial (R : Type*) [CommRing R] (n : ℕ) :
    Bell.complete (fun _ => (X : R[X])) n = touchardPolynomial R n := by
  rw [bell_complete_const, touchardPolynomial]

/-- Spivey's identity for Touchard polynomials over `ℚ`. -/
theorem touchardPolynomial_add_eq_rat (m n : ℕ) :
    touchardPolynomial ℚ (m + n) = ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
      (Nat.stirlingSecond m j : ℚ[X]) * X ^ j *
        ((n.choose k : ℚ[X]) * (touchardPolynomial ℚ k * (j : ℚ[X]) ^ (n - k))) := by
  have h := spivey_touchard ℚ[X] X m n
  simpa only [bell_complete_X_eq_touchardPolynomial] using h

/-- The image of `T_k` under a coefficient map. -/
theorem map_touchardPolynomial {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (k : ℕ) :
    (touchardPolynomial R k).map f = touchardPolynomial S k := by
  rw [touchardPolynomial, touchardPolynomial, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_natCast, Polynomial.map_pow, Polynomial.map_X]

/-- Spivey's identity for Touchard polynomials over `ℤ`. -/
theorem touchardPolynomial_add_eq_int (m n : ℕ) :
    touchardPolynomial ℤ (m + n) = ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
      (Nat.stirlingSecond m j : ℤ[X]) * X ^ j *
        ((n.choose k : ℤ[X]) * (touchardPolynomial ℤ k * (j : ℤ[X]) ^ (n - k))) := by
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_natCast, Polynomial.map_pow,
    Polynomial.map_X, map_touchardPolynomial]
  exact touchardPolynomial_add_eq_rat m n

/-- **Spivey's identity for Touchard polynomials** over any commutative ring:
`T_{m+n} = ∑_{j ≤ m} ∑_{k ≤ n} S(m,j) X^j C(n,k) T_k j^{n-k}`. -/
theorem touchardPolynomial_add_eq (R : Type*) [CommRing R] (m n : ℕ) :
    touchardPolynomial R (m + n) = ∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
      (Nat.stirlingSecond m j : R[X]) * X ^ j *
        ((n.choose k : R[X]) * (touchardPolynomial R k * (j : R[X]) ^ (n - k))) := by
  have h := congrArg (Polynomial.map (Int.castRingHom R)) (touchardPolynomial_add_eq_int m n)
  simpa only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_natCast, Polynomial.map_pow,
    Polynomial.map_X, map_touchardPolynomial] using h

/-- **The polynomial Touchard congruence:** `T_{n+p} = T_{n+1} + X^p T_n` in `(ZMod p)[X]`
for a prime `p`. -/
theorem touchardPolynomial_add_prime (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    touchardPolynomial (ZMod p) (n + p) =
      touchardPolynomial (ZMod p) (n + 1) + X ^ p * touchardPolynomial (ZMod p) n := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  rw [Nat.add_comm n, touchardPolynomial_add_eq (ZMod (q + 2)) (q + 2) n, Finset.sum_range_succ,
    Finset.sum_range_succ', Finset.sum_range_succ']
  -- the term `j = 0` vanishes
  rw [Nat.stirlingSecond_succ_zero, Nat.cast_zero]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  -- the terms `1 < j < p` vanish modulo `p`
  rw [Finset.sum_eq_zero fun j hj => ?_, zero_add]
  swap
  · have hj : j < q := Finset.mem_range.mp hj
    have hz : ((Nat.stirlingSecond (q + 2) (j + 1 + 1) : ℕ) : (ZMod (q + 2))[X]) = 0 := by
      rw [← C_eq_natCast, stirlingSecond_prime_eq_zero_zmod (q + 2) (j + 1 + 1) (by omega) (by omega),
        map_zero]
    rw [hz]
    simp
  -- the term `j = 1` is `T_{n+1}`, the term `j = p` is `X^p T_n`
  have h1' : Nat.stirlingSecond (q + 2) (0 + 1) = 1 := Nat.stirlingSecond_one_right (q + 1)
  have hp0 : ((q + 2 : ℕ) : (ZMod (q + 2))[X]) = 0 := by
    rw [← C_eq_natCast, ZMod.natCast_self, map_zero]
  rw [h1', Nat.stirlingSecond_self, Nat.cast_one, hp0]
  simp only [one_mul, one_pow, mul_one, zero_add, pow_one, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero]
  have h2 : ∑ k ∈ Finset.range (n + 1), (n.choose k : (ZMod (q + 2))[X]) *
      (touchardPolynomial (ZMod (q + 2)) k * (0 : (ZMod (q + 2))[X]) ^ (n - k))
      = touchardPolynomial (ZMod (q + 2)) n := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      one_mul, Finset.sum_eq_zero fun k hk => ?_, zero_add]
    have hkn : k < n := Finset.mem_range.mp hk
    rw [zero_pow (by omega), mul_zero, mul_zero]
  rw [← Finset.mul_sum, ← Finset.mul_sum, h2, ← touchardPolynomial_succ]

end Fabius
