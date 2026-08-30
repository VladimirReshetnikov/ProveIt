import FabiusFunction.DigitCharacterCongruence

/-!
# One binary digit as a difference of dyadic floors

The Thue–Morse atlas extracts a single binary digit as

`b_j(n) = ⌊n / 2^j⌋ - 2⌊n / 2^(j+1)⌋`  (`p1:eq:bit-floor`),

while the corpus carries the equivalent *residue* form,
`Fabius.testBit_iff_div_two_pow_mod_two`: the `j`-th bit is set exactly
when `⌊n/2^j⌋` is odd.  The two are the same statement — the
difference is the remainder, since `⌊n/2^(j+1)⌋ = ⌊⌊n/2^j⌋/2⌋` — but
only one of them was a theorem, so a crosswalk between the atlas
display and the corpus had to say "equivalent to" rather than name a
declaration.  This module supplies the difference form itself, so the
citation can be exact.

The general shape is worth stating separately from the digit: for any
`m`, `m - 2⌊m/2⌋` is `m % 2`, and the dyadic floors compose. Both
steps are `omega` once `Nat.div_div_eq_div_mul` has flattened the
iterated division.

* `Fabius.div_two_pow_succ_eq_div_div` — `⌊n/2^(j+1)⌋ = ⌊⌊n/2^j⌋/2⌋`;
* `Fabius.sub_two_mul_div_two` — `m - 2⌊m/2⌋ = m % 2`;
* `Fabius.div_two_pow_sub_two_mul_div_two_pow_succ` — **the atlas
  display** as an identity of naturals;
* `Fabius.testBit_toNat_eq_div_sub_two_mul_div` — the same with the
  left side written as the bit itself.
-/

set_option autoImplicit false

namespace Fabius

/-- Dyadic floors compose: `⌊n / 2^(j+1)⌋ = ⌊⌊n / 2^j⌋ / 2⌋`. -/
theorem div_two_pow_succ_eq_div_div (n j : ℕ) :
    n / 2 ^ (j + 1) = n / 2 ^ j / 2 := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

/-- `m - 2⌊m/2⌋ = m % 2`. -/
theorem sub_two_mul_div_two (m : ℕ) : m - 2 * (m / 2) = m % 2 := by
  omega

/-- **The atlas's digit extraction** `p1:eq:bit-floor`, as an identity
of naturals:

`⌊n / 2^j⌋ - 2⌊n / 2^(j+1)⌋ = ⌊n / 2^j⌋ % 2`,

the right side being the `j`-th binary digit of `n`. -/
theorem div_two_pow_sub_two_mul_div_two_pow_succ (n j : ℕ) :
    n / 2 ^ j - 2 * (n / 2 ^ (j + 1)) = n / 2 ^ j % 2 := by
  rw [div_two_pow_succ_eq_div_div]
  exact sub_two_mul_div_two _

/-- The same with the left side written as the bit itself: the `j`-th
binary digit of `n`, as a natural number, is the difference of the two
dyadic floors. -/
theorem testBit_toNat_eq_div_sub_two_mul_div (n j : ℕ) :
    (if n.testBit j then 1 else 0)
      = n / 2 ^ j - 2 * (n / 2 ^ (j + 1)) := by
  rw [div_two_pow_sub_two_mul_div_two_pow_succ]
  by_cases hb : n.testBit j
  · rw [if_pos hb]
    exact (testBit_iff_div_two_pow_mod_two.mp hb).symm
  · rw [if_neg hb]
    have h := Nat.mod_two_eq_zero_or_one (n / 2 ^ j)
    rcases h with h0 | h1
    · exact h0.symm
    · exact absurd (testBit_iff_div_two_pow_mod_two.mpr h1) hb

end Fabius
