import FabiusFunction.BitPositionGenerating
import FabiusFunction.FiniteQBinomialCore

/-!
# The finite q-Pochhammer as a Thue--Morse block sum

`BitPositionGenerating` proves the bit-position generating identity

`∏_{j<N} (1 + y qʲ) = ∑_{n<2ᴺ} y^{w(n)} q^{σ(n)}`,

where `w(n)` is the binary digit sum and `σ(n) = bitPositionSum n` is the sum
of the positions of the one bits of `n`.  Nothing in the atlas connects that
identity to the finite q-Pochhammer symbol, even though the connection is the
single substitution `y = -z`: the alternating sign it produces is exactly the
Thue--Morse sign `ε(n) = (-1)^{w(n)}`.

This module records the resulting bridge,

`∑_{n<2ᴺ} ε(n) z^{w(n)} q^{σ(n)} = (z; q)_N`,

over an arbitrary commutative ring and with no hypothesis on `z` or `q`.  It
is a *bigraded* refinement: the two statistics `w` and `σ` on the dyadic
block `n < 2ᴺ` carry, respectively, the `z`-degree and the `q`-degree of the
q-Pochhammer product.  Both univariate faces are already in the atlas — at
`q = 1` it is the binomial weight enumerator of `ThueMorseBooleanCube`, and
the graded pieces of the `z`-expansion are the Gaussian coefficients of
`BitPositionQBinomial` — but the two-variable statement that has them as
specializations was missing, and with it the observation that a q-Pochhammer
*is* a Thue--Morse alternating sum.

The `z = 1` face is the sharpest: `(1; q)_N = 0` for `N ≥ 1`, because the
`j = 0` factor is `1 - q⁰ = 0`.  So the dyadic block sum of `ε(n) q^{σ(n)}`
vanishes identically for every `q` and every `N ≥ 1` — a Prouhet-type
cancellation graded by bit position rather than by degree.

## Main results

* `sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn` — the bridge
  `∑_{n<2ᴺ} ε(n) z^{w(n)} q^{σ(n)} = (z; q)_N`.
* `sum_thueMorseSign_mul_pow_bitPositionSum_eq_zero` — its `z = 1` face:
  the bit-position-graded block sum vanishes for `N ≥ 1`.
* `sum_thueMorseSign_mul_pow_binaryWeight` — its `q = 1` face,
  `∑_{n<2ᴺ} ε(n) z^{w(n)} = (1 - z)^N`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- **The finite q-Pochhammer is a Thue--Morse block sum.**  Over every
commutative ring and for all `z` and `q`,

`∑_{n<2ᴺ} ε(n) · z^{w(n)} · q^{σ(n)} = (z; q)_N`,

where `w` is the binary digit sum, `σ` the sum of one-bit positions, and
`ε(n) = (-1)^{w(n)}` the Thue--Morse sign.

The proof is the bit-position generating identity
`prod_one_add_mul_pow_bitPositionSum` at `y = -z`; the sign it releases is
the Thue--Morse sign by definition.  No hypothesis on `z` or `q` is used, so
the identity holds at roots of unity, in positive characteristic, and in the
presence of zero divisors. -/
theorem sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn
    {R : Type*} [CommRing R] (z q : R) (N : ℕ) :
    ∑ n ∈ Finset.range (2 ^ N),
        ((thueMorseSign n : ℤ) : R) * z ^ binaryWeight n *
          q ^ bitPositionSum n =
      finiteQPochhammerIn z q N := by
  have hprod : ∏ j ∈ Finset.range N, (1 - z * q ^ j) =
      ∏ j ∈ Finset.range N, (1 + (-z) * q ^ j) :=
    Finset.prod_congr rfl fun j _ => by ring
  rw [finiteQPochhammerIn, hprod, prod_one_add_mul_pow_bitPositionSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [neg_pow, thueMorseSign]
  push_cast
  ring

/-- **Bit-position Prouhet cancellation.**  For `N ≥ 1` and every `q` in
every commutative ring,

`∑_{n<2ᴺ} ε(n) q^{σ(n)} = 0`.

This is the `z = 1` face of
`sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn`: the `j = 0`
factor of `(1; q)_N` is `1 - 1 · q⁰ = 0`.  Unlike ordinary Prouhet
cancellation, which needs the summand to be a polynomial of degree below
`N`, the grading here is by bit position and the statement holds for every
`q` at once. -/
theorem sum_thueMorseSign_mul_pow_bitPositionSum_eq_zero
    {R : Type*} [CommRing R] (q : R) {N : ℕ} (hN : 0 < N) :
    ∑ n ∈ Finset.range (2 ^ N),
        ((thueMorseSign n : ℤ) : R) * q ^ bitPositionSum n = 0 := by
  have hbase : ∑ n ∈ Finset.range (2 ^ N),
      ((thueMorseSign n : ℤ) : R) * (1 : R) ^ binaryWeight n *
        q ^ bitPositionSum n = finiteQPochhammerIn 1 q N :=
    sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn 1 q N
  simp only [one_pow, mul_one] at hbase
  have hzero : finiteQPochhammerIn (1 : R) q N = 0 := by
    rw [finiteQPochhammerIn]
    refine Finset.prod_eq_zero (Finset.mem_range.mpr hN) ?_
    simp
  rw [hbase, hzero]

/-- **The binomial weight enumerator, from the bigraded bridge.**  For every
`z` in every commutative ring,

`∑_{n<2ᴺ} ε(n) z^{w(n)} = (1 - z)^N`.

This is the `q = 1` face of
`sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn`. -/
theorem sum_thueMorseSign_mul_pow_binaryWeight
    {R : Type*} [CommRing R] (z : R) (N : ℕ) :
    ∑ n ∈ Finset.range (2 ^ N),
        ((thueMorseSign n : ℤ) : R) * z ^ binaryWeight n = (1 - z) ^ N := by
  have hbase : ∑ n ∈ Finset.range (2 ^ N),
      ((thueMorseSign n : ℤ) : R) * z ^ binaryWeight n *
        (1 : R) ^ bitPositionSum n = finiteQPochhammerIn z 1 N :=
    sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn z 1 N
  simp only [one_pow, mul_one] at hbase
  rw [hbase, finiteQPochhammerIn]
  simp [Finset.prod_const]

end Fabius
