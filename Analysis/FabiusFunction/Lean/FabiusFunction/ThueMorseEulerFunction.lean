import FabiusFunction.QPochhammerMultiplicativeDissection
import FabiusFunction.ThueMorseInfiniteProduct

/-!
# Euler's function as a product of Thue–Morse generating functions

Write `E(z) = ∑' n, ε(n)·zⁿ` for the Thue–Morse generating function, whose
lacunary product form `E(z) = ∏'_j (1 - z^(2^j))` is
`tsum_thueMorseSign_mul_pow_complex`.  This module proves, for every complex
`q` with `‖q‖ < 1`,

`(q;q)_∞ = ∏'_{k≥0} E(q^(2k+1)) = ∏'_{k≥0} ∑'_n ε(n)·q^((2k+1)·n)`:

**Euler's function is the infinite product, over the odd multipliers
`m = 2k+1`, of the Thue–Morse generating function evaluated at `q^m`.**

The mechanism is the *multiplicative* dissection of the index set: every
`n ≥ 1` factors uniquely as `odd · 2-power`, so the double family
`(k, j) ↦ 1 - q^((2k+1)·2^j)` is a reindexing of the family
`n ↦ 1 - q^(n+1)` whose product is `(q;q)_∞`.  Grouping the pairs by their
odd part `2k+1` leaves, in each group, exactly the lacunary product
`∏'_j (1 - (q^(2k+1))^(2^j))` that the Thue–Morse identity sums.

## Relation to the rest of the atlas

The Thue–Morse and `q`-Pochhammer layers already meet at the *finite*,
*additive*, bigraded level, by a different mechanism:

* `sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn`
  (`ThueMorseQPochhammer`) writes the finite symbol `(z;q)_N` as the
  Thue–Morse alternating sum `∑_{n<2^N} ε(n)·z^(w n)·q^(σ n)` over an
  arbitrary commutative ring, with no convergence hypothesis; and
* `two_pow_nat_sq_mul_qPochhammer_half_eq_thueMorse_sum`
  (`GeneralLinearThueMorseSum`) specializes that to the dyadic Fabius
  prefactor `2^{n²}·(1/2;1/2)_n`, so the *finite* prefactor of the Fabius
  central formula is already a Thue–Morse sum.  (The constant
  `(1/2;1/2)_∞` is the limit of those prefactors, not one of them.)

What is new here is the *infinite*, *multiplicative* counterpart: the whole
Euler function, not a finite truncation, expressed through the Thue–Morse
generating function itself rather than through a bigraded sign sum.

The additive companion in the corpus is `qPochhammerInfIn_dissection`, the
residue-class dissection `(a;q)_∞ = ∏_{s<r} (a q^s ; q^r)_∞`.  The two are
not independent: iterating its `r = 2` instance
`qPochhammerInfIn_self_eq_odd_mul_even` (`PartitionDistinctOdd`),
`(q;q)_∞ = (q;q²)_∞·(q²;q²)_∞`, groups the same double family the other way
round — `2`-power first — and reaches a related product by a cheaper route.
The grouping proved here is the odd-part-first one, which does need the
`ℕ × ℕ` reindexing.

## Scope

Everything below is stated over `ℂ`.  The Thue–Morse product-to-sum identity
exists in the corpus only over `ℝ` (`tsum_thueMorseSign_mul_pow`) and over
`ℂ` (`tsum_thueMorseSign_mul_pow_complex`); there is no version over a
general complete normed field, so the final identity is not stated at that
generality here.  The purely combinatorial steps —
`oddTwoPowEquiv` and `qPochhammerInfIn_self_eq_tprod_pair` — are of course
independent of the coefficient field, and the latter needs no hypothesis on
`q` at all, since transporting a `tprod` along an equivalence is
unconditional.

The regrouping technique follows `rvachevFourierProduct_eq_canonical`
(`SincCanonicalProduct`).  Its `dyadicFactorEquiv` is a precedent for the
technique only, not for the map: that one is a *fibered* equivalence
`ℕ × ℕ ≃ Σ m, Fin (v₂(m+1) + 1)` whose second coordinate ranges over all
positive integers, whereas `oddTwoPowEquiv` below is a plain bijection
`ℕ × ℕ ≃ ℕ` with the cofactor constrained to be odd.

## Main declarations

The purely `q`-series half of the argument — the bijection `oddTwoPowEquiv`,
the convergence of the double family, the flattened product
`qPochhammerInfIn_self_eq_tprod_pair` and the odd-part-first grouping
`qPochhammerInfIn_self_eq_tprod_lacunary` — carries no Thue--Morse content and
lives in `QPochhammerMultiplicativeDissection`, which this module imports.
What remains here is only the identification of each lacunary factor with a
value of the Thue--Morse generating function.

* `qPochhammerInfIn_self_eq_tprod_tsum_thueMorseSign` and
  `qPochhammerInfIn_self_eq_tprod_tsum_thueMorseSign_pow` — **the identity**,
  in its two equivalent exponent normalizations `q^((2k+1)·n)` and
  `(q^(2k+1))^n`.
-/

set_option autoImplicit false

namespace Fabius

/-- **Euler's function is a product of Thue–Morse generating functions.**
For every complex `q` with `‖q‖ < 1`,

`(q;q)_∞ = ∏'_{k≥0} ∑'_n ε(n)·q^((2k+1)·n)`,

the infinite product over the *odd* multipliers `m = 2k+1` of the Thue–Morse
generating function `E` evaluated at `q^m`.

The `k = 0` factor is `E(q)` itself, so the identity contains the atlas's
opening product `tsum_thueMorseSign_mul_pow_complex` as its first term.  Its
finite, additive, bigraded counterpart is
`sum_thueMorseSign_mul_pow_bigraded_eq_finiteQPochhammerIn`. -/
theorem qPochhammerInfIn_self_eq_tprod_tsum_thueMorseSign {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q =
      ∏' k : ℕ, ∑' n : ℕ, (thueMorseSign n : ℂ) * q ^ ((2 * k + 1) * n) := by
  rw [qPochhammerInfIn_self_eq_tprod_lacunary hq]
  refine tprod_congr fun k => ?_
  have hnorm : ‖q ^ (2 * k + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  rw [← tsum_thueMorseSign_mul_pow_complex hnorm]
  exact tsum_congr fun n => by rw [pow_mul]

/-- The same identity with the inner series written at the nome `q^(2k+1)`:
`(q;q)_∞ = ∏'_k E(q^(2k+1))`, where `E(z) = ∑' n, ε(n)·zⁿ`.  This is the
form in which the `k`-th factor is literally a value of the Thue–Morse
generating function. -/
theorem qPochhammerInfIn_self_eq_tprod_tsum_thueMorseSign_pow {q : ℂ}
    (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q =
      ∏' k : ℕ, ∑' n : ℕ, (thueMorseSign n : ℂ) * (q ^ (2 * k + 1)) ^ n := by
  rw [qPochhammerInfIn_self_eq_tprod_tsum_thueMorseSign hq]
  exact tprod_congr fun k => tsum_congr fun n => by rw [pow_mul]

end Fabius
