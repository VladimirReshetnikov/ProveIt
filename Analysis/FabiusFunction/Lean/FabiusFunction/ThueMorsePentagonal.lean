import FabiusFunction.ThueMorseQPochhammerInfinite
import FabiusFunction.EulerPartitionRecurrence

/-!
# Euler's pentagonal number theorem as a Thue--Morse digit sum

`ThueMorseQPochhammerInfinite` proves the bigraded bridge

`∑'_n ε(n)·z^{w(n)}·q^{σ(n)} = (z;q)_∞`,

where `w` is the binary digit sum, `σ = bitPositionSum` the sum of the
positions of the one bits, and `ε(n) = (-1)^{w(n)}` the Thue--Morse sign.  Its
diagonal `z = q` collapses the two gradings into one, because

`w(n) + σ(n) = ∑_{j ∈ bits(n)} (j + 1)`,

so the exponent runs over the sums of finite sets of *positive* integers, each
exactly once — which is precisely the index set of Euler's function
`(q;q)_∞ = ∏_{m≥1} (1 - q^m)`.

Composing with `hasSum_pentagonalCoeff_mul_pow` of `EulerPartitionRecurrence`,
which already lands on `qPochhammerInfIn q q`, turns Euler's pentagonal number
theorem into a statement relating two very different digit statistics:

`∑'_n (-1)^{w(n)} q^{w(n)+σ(n)} = ∑'_n e(n) q^n`,

with `e` the pentagonal coefficients supported on the generalized pentagonal
numbers `j(3j-1)/2`.  The left side is indexed by the binary expansion of `n`;
the right is supported on a sparse quadratic sequence.

Nothing here reproves any `q`-series fact: the pentagonal theorem is consumed
from `EulerPartitionRecurrence` unchanged, and the bridge from
`ThueMorseQPochhammerInfinite`.

## Main results

* `binaryWeight_add_bitPositionSum` — the diagonal exponent
  `w(n) + σ(n) = ∑_{j ∈ bits(n)} (j+1)`.
* `tsum_thueMorseSign_mul_pow_digitWeight_eq_qPochhammerInfIn` — the diagonal
  `z = q` of the bigraded bridge: `∑'_n ε(n) q^{w(n)+σ(n)} = (q;q)_∞`.
* `tsum_thueMorseSign_mul_pow_digitWeight_eq_tsum_pentagonalCoeff` — the
  pentagonal number theorem in Thue--Morse digit form.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **The diagonal exponent.**  Summing the two binary statistics adds one to
each bit position: `w(n) + σ(n) = ∑_{j ∈ bits(n)} (j + 1)`.  This is why the
diagonal `z = q` of the bigraded bridge lands on Euler's function — the
exponent enumerates the sums of finite sets of positive integers. -/
theorem binaryWeight_add_bitPositionSum (n : ℕ) :
    binaryWeight n + bitPositionSum n = ∑ j ∈ bitSupport n, (j + 1) := by
  have h : ∑ j ∈ bitSupport n, (j + 1)
      = (∑ j ∈ bitSupport n, j) + (bitSupport n).card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  rw [h, bitPositionSum, card_bitSupport]
  omega

/-- **The diagonal bridge.**  For every `q` with `‖q‖ < 1`,

`∑'_n ε(n) q^{w(n)+σ(n)} = (q;q)_∞`.

This is `tsum_thueMorseSign_mul_pow_bigraded_eq_qPochhammerInfIn` at `z = q`,
with the two powers merged. -/
theorem tsum_thueMorseSign_mul_pow_digitWeight_eq_qPochhammerInfIn
    {q : ℂ} (hq : ‖q‖ < 1) :
    ∑' n : ℕ, (thueMorseSign n : ℂ) * q ^ (binaryWeight n + bitPositionSum n) =
      qPochhammerInfIn q q := by
  rw [← tsum_thueMorseSign_mul_pow_bigraded_eq_qPochhammerInfIn q hq]
  exact tsum_congr fun n => by rw [pow_add, ← mul_assoc]

/-- **Euler's pentagonal number theorem as a Thue--Morse digit sum.**  For
every `q` with `‖q‖ < 1`,

`∑'_n (-1)^{w(n)} q^{w(n)+σ(n)} = ∑'_n e(n) q^n`,

where `e` is the pentagonal coefficient sequence, supported on the generalized
pentagonal numbers.  Both sides are `(q;q)_∞`: the left by the diagonal bridge,
the right by `hasSum_pentagonalCoeff_mul_pow`, which is consumed unchanged. -/
theorem tsum_thueMorseSign_mul_pow_digitWeight_eq_tsum_pentagonalCoeff
    {q : ℂ} (hq : ‖q‖ < 1) :
    ∑' n : ℕ, (thueMorseSign n : ℂ) * q ^ (binaryWeight n + bitPositionSum n) =
      ∑' n : ℕ, pentagonalCoeff n * q ^ n := by
  rw [tsum_thueMorseSign_mul_pow_digitWeight_eq_qPochhammerInfIn hq,
    (hasSum_pentagonalCoeff_mul_pow hq).tsum_eq]

end Fabius
