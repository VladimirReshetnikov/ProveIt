import FabiusFunction.FabiusGeneralLinearDenominator
import FabiusFunction.ThueMorseQPochhammer

/-!
# The order of `GL_n` as a Thue--Morse alternating sum

Two identities established elsewhere in the atlas compose into one.

`FabiusGeneralLinearDenominator` shows that over a finite field with
`Q = |K|` elements the order of the general linear group is a q-Pochhammer
prefactor,

`|GL_n(K)| = Q^{n^2} · (1/Q; 1/Q)_n`,

and `ThueMorseQPochhammer` shows that a finite q-Pochhammer is a Thue--Morse
block sum bigraded by the binary digit sum `w` and the bit-position sum `σ`,

`(z; q)_N = ∑_{m<2ᴺ} ε(m) z^{w(m)} q^{σ(m)}`.

Substituting the first into the second at `z = q = 1/Q` and `N = n` gives a
closed alternating expression for the group order in which the only
arithmetic input is the binary expansion of the summation index:

`|GL_n(K)| = ∑_{m<2ⁿ} ε(m) · Q^{n^2 - w(m) - σ(m)}`.

The exponent is written here as `Q^{n^2}·(Q⁻¹)^{w(m)}·(Q⁻¹)^{σ(m)}` to avoid
truncated natural subtraction; it is genuinely non-negative, since
`w(m) + σ(m) ≤ n + C(n,2) = C(n+1,2) ≤ n^2` for `m < 2ⁿ`, with the minimum
exponent `C(n,2)` attained at `m = 2ⁿ - 1`.

For `K = 𝔽_2` the left-hand side is the denominator of the exact dyadic
values of the Fabius function (`FabiusGeneralLinearDenominator`), so this is
also a Thue--Morse formula for that denominator: `1, 1, 6, 168, 20160,
9999360, 20158709760, …`.

## Main results

* `cast_card_generalLinearGroup_eq_thueMorse_sum` — the alternating-sum
  formula over an arbitrary finite field.
* `cast_card_generalLinearGroup_zmod_two_eq_thueMorse_sum` — its `𝔽_2` face,
  which is the Fabius dyadic denominator.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- **The order of `GL_n(K)` is a Thue--Morse alternating sum.**  Over every
finite field with `Q = |K|` elements,

`|GL_n(K)| = Q^{n^2} · ∑_{m<2ⁿ} ε(m) · (1/Q)^{w(m)} · (1/Q)^{σ(m)}`,

where `w` is the binary digit sum, `σ` the sum of one-bit positions, and `ε`
the Thue--Morse sign.  Collecting the powers, the summand is
`ε(m) Q^{n^2 - w(m) - σ(m)}` with a non-negative exponent.

The order of `GL_n` itself is Mathlib's `Matrix.card_GL_field`; this is a
restatement of it, not a new proof of it. -/
theorem cast_card_generalLinearGroup_eq_thueMorse_sum
    {K : Type*} [Field K] [Fintype K] (n : ℕ) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin n) K) : ℚ) =
      (Fintype.card K : ℚ) ^ (n ^ 2) *
        ∑ m ∈ Finset.range (2 ^ n),
          ((thueMorseSign m : ℤ) : ℚ) *
              ((Fintype.card K : ℚ)⁻¹) ^ binaryWeight m *
            ((Fintype.card K : ℚ)⁻¹) ^ bitPositionSum m := by
  rw [cast_card_generalLinearGroup_eq_pow_sq_mul_qPochhammer (K := K) n,
    ← sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn]

/-- The `𝔽_2` face: a Thue--Morse alternating sum for the denominator of the
exact dyadic Fabius values.

`|GL_n(𝔽_2)| = 2^{n^2} · ∑_{m<2ⁿ} ε(m) 2^{-w(m)} 2^{-σ(m)}`,

giving `1, 1, 6, 168, 20160, 9999360, 20158709760, …`. -/
theorem cast_card_generalLinearGroup_zmod_two_eq_thueMorse_sum (n : ℕ) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : ℚ) =
      (2 : ℚ) ^ (n ^ 2) *
        ∑ m ∈ Finset.range (2 ^ n),
          ((thueMorseSign m : ℤ) : ℚ) *
              ((2 : ℚ)⁻¹) ^ binaryWeight m *
            ((2 : ℚ)⁻¹) ^ bitPositionSum m := by
  have h := cast_card_generalLinearGroup_eq_thueMorse_sum (K := ZMod 2) n
  rw [ZMod.card] at h
  simpa using h

/-- The dyadic Fabius prefactor as a Thue--Morse alternating sum:

`2^{n^2} (1/2; 1/2)_n = 2^{n^2} ∑_{m<2ⁿ} ε(m) 2^{-w(m)} 2^{-σ(m)}`,

which is the group order `|GL_n(𝔽_2)|`. -/
theorem two_pow_nat_sq_mul_qPochhammer_half_eq_thueMorse_sum (n : ℕ) :
    (2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n =
      (2 : ℚ) ^ (n ^ 2) *
        ∑ m ∈ Finset.range (2 ^ n),
          ((thueMorseSign m : ℤ) : ℚ) *
              ((2 : ℚ)⁻¹) ^ binaryWeight m *
            ((2 : ℚ)⁻¹) ^ bitPositionSum m := by
  rw [two_pow_nat_sq_mul_qPochhammer_half_eq_card_GL,
    cast_card_generalLinearGroup_zmod_two_eq_thueMorse_sum]

end Fabius
