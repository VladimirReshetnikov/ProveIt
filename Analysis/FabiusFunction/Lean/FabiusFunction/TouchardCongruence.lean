import FabiusFunction.BellShiftEGF
import FabiusFunction.StirlingBasisChange
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Touchard's congruence for Bell numbers

For a prime `p`, `B(n + p) ≡ B(n) + B(n+1) (mod p)`.

The proof is Spivey's identity `B(n+p) = ∑_{j ≤ p} ∑_{k ≤ n} S(p,j) C(n,k) B(k) j^{n-k}`
read modulo `p`: the Stirling numbers `S(p,j)` with `1 < j < p` vanish modulo `p`
(surjection formula and Fermat's little theorem), the term `j = 1` is
`∑_k C(n,k) B(k) = B(n+1)`, and the term `j = p` reduces to `B(n)` because
`p^{n-k} ≡ 0` for `k < n`.

## Main results

* `stirlingSecond_prime_eq_zero_zmod`: `S(p,k) = 0` in `ZMod p` for `1 < k < p`.
* `bell_add_prime_modEq`: Touchard's congruence.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- For a prime `p` and `1 < k < p`, `p ∣ S(p,k)`: in `ZMod p`, the surjection formula
and Fermat's little theorem give `k! S(p,k) = ∑_j (-1)^{k-j} C(k,j) j = k! S(1,k) = 0`. -/
theorem stirlingSecond_prime_eq_zero_zmod (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (hk1 : 1 < k)
    (hkp : k < p) : (Nat.stirlingSecond p k : ZMod p) = 0 := by
  have hz := congrArg (Int.cast : ℤ → ZMod p) (factorial_mul_stirlingSecond_eq_sum p k)
  have hz1 := congrArg (Int.cast : ℤ → ZMod p) (factorial_mul_stirlingSecond_eq_sum 1 k)
  push_cast at hz hz1
  simp only [ZMod.pow_card, pow_one] at hz hz1
  rw [Nat.stirlingSecond_eq_zero_of_lt hk1, Nat.cast_zero, mul_zero] at hz1
  rw [← hz1] at hz
  have hfac : (k.factorial : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial hp.out]
    omega
  exact (mul_eq_zero.mp hz).resolve_left hfac

/-- **Touchard's congruence:** `B(n + p) ≡ B(n) + B(n + 1) (mod p)` for a prime `p`. -/
theorem bell_add_prime_modEq (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    Nat.bell (n + p) ≡ Nat.bell n + Nat.bell (n + 1) [MOD p] := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have hs := spivey (q + 2) n
  rw [Nat.add_comm (q + 2) n] at hs
  have hc := congrArg (Nat.cast : ℕ → ZMod (q + 2)) hs
  push_cast at hc ⊢
  rw [hc, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
  -- the term `j = 0` vanishes
  rw [Nat.stirlingSecond_succ_zero, Nat.cast_zero]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  -- the terms `1 < j < p` vanish modulo `p`
  rw [Finset.sum_eq_zero fun j hj => ?_, zero_add]
  swap
  · have hj : j < q := Finset.mem_range.mp hj
    rw [show j + 1 + 1 = j + 2 by omega,
      stirlingSecond_prime_eq_zero_zmod (q + 2) (j + 2) (by omega) (by omega)]
    simp
  -- the term `j = 1` is `B(n+1)`, the term `j = p` is `B(n)`
  have h1' : Nat.stirlingSecond (q + 2) (0 + 1) = 1 := Nat.stirlingSecond_one_right (q + 1)
  rw [h1', Nat.stirlingSecond_self, Nat.cast_one]
  simp only [one_mul, one_pow, mul_one, ZMod.natCast_self]
  have h1 : ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : ZMod (q + 2)) *
      ((Nat.bell k : ℕ) : ZMod (q + 2)) = (Nat.bell (n + 1) : ZMod (q + 2)) := by
    rw [bell_succ_eq_sum_choose]
    push_cast
    rfl
  have h2 : ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : ZMod (q + 2)) *
      (((Nat.bell k : ℕ) : ZMod (q + 2)) * (0 : ZMod (q + 2)) ^ (n - k))
      = (Nat.bell n : ZMod (q + 2)) := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      one_mul, Finset.sum_eq_zero fun k hk => ?_, zero_add]
    have hkn : k < n := Finset.mem_range.mp hk
    rw [zero_pow (by omega), mul_zero, mul_zero]
  rw [h1, h2]
  exact add_comm _ _

end Fabius
