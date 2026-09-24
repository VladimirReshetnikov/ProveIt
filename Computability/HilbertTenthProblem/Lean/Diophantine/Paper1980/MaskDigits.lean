import Diophantine.Paper1982.Carries

/-!
# Bitwise masks read digit by digit in a power-of-two radix

For `B = 2^m` with `0 < m`, the condition `X &&& M = 0` (the mask `τ₂(X, M) = 0` of the
certificate systems) is equivalent to the same condition on every base-`B`
digit: `(X / Bⁱ % B) &&& (M / Bⁱ % B) = 0` for all `i`.  This is how the
first mask `g & (q² − 1 − b l) = 0` is read in Section 4 of the affine-radix
proofs: its digits are `B − 1` off the indicator support (forcing the
digit of `g` to vanish) and `H₀ = H + 3` on the support (forcing that single
bit of the digit of `g` to be clear).  The lemma is pure bit arithmetic and
is independent of the certificate version.
-/

namespace Jones1980

open Nat

/-- A bit of a base-`2^m` digit is the corresponding bit of the number. -/
theorem testBit_digit (X m i t : ℕ) :
    (X / 2 ^ (m * i) % 2 ^ m).testBit t = (decide (t < m) && X.testBit (t + m * i)) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

/-- `X &&& M = 0` if and only if every base-`2^m` digit of `X` is disjoint from the
corresponding digit of `M`. -/
theorem land_eq_zero_iff_digits (X M m : ℕ) (hm : 0 < m) :
    X &&& M = 0 ↔ ∀ i, (X / 2 ^ (m * i) % 2 ^ m) &&& (M / 2 ^ (m * i) % 2 ^ m) = 0 := by
  simp only [Jones1982.land_eq_zero_iff, testBit_digit]
  constructor
  · intro h i t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
    right
    exact h _ ht.2
  · intro h p hp
    have := h (p / m) (p % m)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, not_lt] at this
    have hpm : p % m < m := Nat.mod_lt _ hm
    have hp' : p % m + m * (p / m) = p := Nat.mod_add_div p m
    rw [hp'] at this
    rcases this ⟨hpm, hp⟩ with h1 | h1
    · omega
    · exact h1

/-- The mask `τ₂(X, M) = 0` read digit by digit. -/
theorem τ_eq_zero_iff_digits (X M m : ℕ) (hm : 0 < m) :
    Jones1982.τ 2 X M = 0 ↔
      ∀ i, (X / 2 ^ (m * i) % 2 ^ m) &&& (M / 2 ^ (m * i) % 2 ^ m) = 0 := by
  rw [Jones1982.τ_two_eq_zero_iff, land_eq_zero_iff_digits X M m hm]

/-- A digit disjoint from `2^m − 1` is zero. -/
theorem digit_zero_of_land_all_ones {x m : ℕ} (hx : x < 2 ^ m) (h : x &&& (2 ^ m - 1) = 0) :
    x = 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx] at h
  exact h

/-- A digit disjoint from the single bit `2^j` has that bit clear: `x / 2^j % 2 = 0`. -/
theorem digit_bit_clear_of_land_pow {x j : ℕ} (h : x &&& 2 ^ j = 0) : x.testBit j = false := by
  have := (Jones1982.land_eq_zero_iff x (2 ^ j)).1 h j
  by_contra hb
  simp only [Bool.not_eq_false] at hb
  have := this hb
  rw [Nat.testBit_two_pow_self] at this
  exact absurd this (by decide)

end Jones1980
