import FabiusFunction.QPochhammerInfinite
import FabiusFunction.ThueMorseInfiniteProduct
import Mathlib.Data.Nat.Factorization.Basic

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

* `oddTwoPowEquiv` — the bijection `(k, j) ↦ (2k+1)·2^j - 1` of `ℕ × ℕ`
  with `ℕ`, i.e. unique factorization into odd part times `2`-power.
* `summable_norm_pow_odd_mul_two_pow`,
  `multipliable_one_sub_pow_odd_mul_two_pow` — absolute convergence of the
  double family.
* `qPochhammerInfIn_self_eq_tprod_pair` — the flattened double product form
  of `(q;q)_∞`, valid for every `q : ℂ`.
* `qPochhammerInfIn_self_eq_tprod_lacunary` — the odd-part-first grouping
  into lacunary products.
* `qPochhammerInfIn_self_eq_tprod_tsum_thueMorseSign` and
  `qPochhammerInfIn_self_eq_tprod_tsum_thueMorseSign_pow` — **the identity**,
  in its two equivalent exponent normalizations `q^((2k+1)·n)` and
  `(q^(2k+1))^n`.
-/

set_option autoImplicit false

namespace Fabius

/-! ## The odd-part / two-power indexing of the positive integers -/

/-- **Unique factorization into odd part times `2`-power**, packaged as an
equivalence `ℕ × ℕ ≃ ℕ`: the pair `(k, j)` encodes the positive integer
`(2k+1)·2^j`, shifted down by one so that the codomain is all of `ℕ`.

The inverse reads the two-power exponent off `Nat.factorization` and the odd
part off `ordCompl[2]`, which `Nat.not_dvd_ordCompl` certifies to be odd. -/
def oddTwoPowEquiv : ℕ × ℕ ≃ ℕ where
  toFun p := (2 * p.1 + 1) * 2 ^ p.2 - 1
  invFun n := ((ordCompl[2] (n + 1) - 1) / 2, (n + 1).factorization 2)
  left_inv p := by
    obtain ⟨k, j⟩ := p
    have hodd : ¬ (2 ∣ 2 * k + 1) := Nat.two_dvd_ne_zero.mpr (by omega)
    have hne : (2 * k + 1) ≠ 0 := by omega
    have hpow : (2 : ℕ) ^ j ≠ 0 := (Nat.two_pow_pos j).ne'
    have hpos : 0 < (2 * k + 1) * 2 ^ j := by positivity
    have h1 : (2 * k + 1) * 2 ^ j - 1 + 1 = (2 * k + 1) * 2 ^ j := by omega
    have hfac : ((2 * k + 1) * 2 ^ j).factorization 2 = j := by
      rw [Nat.factorization_mul hne hpow, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hodd,
        Nat.factorization_pow_self Nat.prime_two, zero_add]
    have hcompl : ordCompl[2] ((2 * k + 1) * 2 ^ j) = 2 * k + 1 := by
      rw [hfac]
      exact Nat.mul_div_cancel _ (Nat.two_pow_pos j)
    have hk : (2 * k + 1 - 1) / 2 = k := by omega
    show ((ordCompl[2] ((2 * k + 1) * 2 ^ j - 1 + 1) - 1) / 2,
        ((2 * k + 1) * 2 ^ j - 1 + 1).factorization 2) = (k, j)
    rw [h1, hcompl, hfac, hk]
  right_inv n := by
    have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
    have hodd : ¬ (2 ∣ ordCompl[2] (n + 1)) :=
      Nat.not_dvd_ordCompl Nat.prime_two hne
    have hmod : ordCompl[2] (n + 1) % 2 = 1 := Nat.two_dvd_ne_zero.mp hodd
    have hc : 2 * ((ordCompl[2] (n + 1) - 1) / 2) + 1 = ordCompl[2] (n + 1) := by
      omega
    have key : (2 * ((ordCompl[2] (n + 1) - 1) / 2) + 1) *
        2 ^ ((n + 1).factorization 2) = n + 1 := by
      rw [hc, mul_comm]
      exact Nat.ordProj_mul_ordCompl_eq_self (n + 1) 2
    show (2 * ((ordCompl[2] (n + 1) - 1) / 2) + 1) *
      2 ^ ((n + 1).factorization 2) - 1 = n
    exact Nat.sub_eq_of_eq_add key

/-- The encoding map of `oddTwoPowEquiv`, unfolded. -/
theorem oddTwoPowEquiv_apply (p : ℕ × ℕ) :
    oddTwoPowEquiv p = (2 * p.1 + 1) * 2 ^ p.2 - 1 := rfl

/-- The encoding map of `oddTwoPowEquiv`, shifted back up: the pair `(k, j)`
names the positive integer `(2k+1)·2^j`. -/
theorem oddTwoPowEquiv_apply_add_one (p : ℕ × ℕ) :
    oddTwoPowEquiv p + 1 = (2 * p.1 + 1) * 2 ^ p.2 := by
  have hpos : 0 < (2 * p.1 + 1) * 2 ^ p.2 := by positivity
  show (2 * p.1 + 1) * 2 ^ p.2 - 1 + 1 = (2 * p.1 + 1) * 2 ^ p.2
  omega

/-! ## Absolute convergence of the double family -/

/-- **Norm-summability of the double family** `(k, j) ↦ q^((2k+1)·2^j)` on
the open unit disc.  The exponent dominates `k + j`, because `2^j ≥ j + 1`
and `2k + 1 ≥ k + 1`, so the norms are dominated termwise by the product of
two geometric series. -/
theorem summable_norm_pow_odd_mul_two_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun p : ℕ × ℕ => ‖q ^ ((2 * p.1 + 1) * 2 ^ p.2)‖ := by
  have hgeom : Summable fun k : ℕ => ‖q‖ ^ k :=
    summable_geometric_of_lt_one (norm_nonneg q) hq
  have hprod : Summable fun p : ℕ × ℕ => ‖q‖ ^ p.1 * ‖q‖ ^ p.2 :=
    hgeom.mul_of_nonneg hgeom (fun _ => by positivity) (fun _ => by positivity)
  refine hprod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
  obtain ⟨k, j⟩ := p
  have hj : j < 2 ^ j := Nat.lt_two_pow_self
  have hmul : (k + 1) * (j + 1) ≤ (2 * k + 1) * 2 ^ j :=
    Nat.mul_le_mul (by omega) (by omega)
  have hexp : k + j ≤ (2 * k + 1) * 2 ^ j := by
    have hring : (k + 1) * (j + 1) = k * j + k + j + 1 := by ring
    omega
  show ‖q ^ ((2 * k + 1) * 2 ^ j)‖ ≤ ‖q‖ ^ k * ‖q‖ ^ j
  calc ‖q ^ ((2 * k + 1) * 2 ^ j)‖ = ‖q‖ ^ ((2 * k + 1) * 2 ^ j) := norm_pow q _
    _ ≤ ‖q‖ ^ (k + j) := pow_le_pow_of_le_one (norm_nonneg q) hq.le hexp
    _ = ‖q‖ ^ k * ‖q‖ ^ j := pow_add ‖q‖ k j

/-- **Multipliability of the double family** `(k, j) ↦ 1 - q^((2k+1)·2^j)`
on the open unit disc: the deviations from `1` are absolutely summable. -/
theorem multipliable_one_sub_pow_odd_mul_two_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun p : ℕ × ℕ => 1 - q ^ ((2 * p.1 + 1) * 2 ^ p.2) := by
  have hsum : Summable fun p : ℕ × ℕ => ‖-(q ^ ((2 * p.1 + 1) * 2 ^ p.2))‖ := by
    simpa only [norm_neg] using summable_norm_pow_odd_mul_two_pow hq
  exact (multipliable_one_add_of_summable hsum).congr fun _ => by ring

/-! ## The multiplicative dissection -/

/-- **The flattened double product**: for every `q : ℂ`,
`(q;q)_∞ = ∏'_{(k,j)} (1 - q^((2k+1)·2^j))`.

This is pure reindexing along `oddTwoPowEquiv`, so it needs no hypothesis on
`q`: transporting an unordered product along an equivalence is
unconditional, and both sides carry Mathlib's junk value `1` together when
the family fails to be multipliable. -/
theorem qPochhammerInfIn_self_eq_tprod_pair (q : ℂ) :
    qPochhammerInfIn q q =
      ∏' p : ℕ × ℕ, (1 - q ^ ((2 * p.1 + 1) * 2 ^ p.2)) := by
  have hshift : (∏' n : ℕ, (1 - q * q ^ n)) = ∏' n : ℕ, (1 - q ^ (n + 1)) :=
    tprod_congr fun n => by rw [pow_succ']
  have hreindex : (∏' p : ℕ × ℕ, (1 - q ^ (oddTwoPowEquiv p + 1))) =
      ∏' n : ℕ, (1 - q ^ (n + 1)) :=
    oddTwoPowEquiv.tprod_eq fun n : ℕ => 1 - q ^ (n + 1)
  have hfactor : (∏' p : ℕ × ℕ, (1 - q ^ (oddTwoPowEquiv p + 1))) =
      ∏' p : ℕ × ℕ, (1 - q ^ ((2 * p.1 + 1) * 2 ^ p.2)) :=
    tprod_congr fun p => by rw [oddTwoPowEquiv_apply_add_one]
  rw [qPochhammerInfIn_eq_tprod, hshift, ← hreindex, hfactor]

/-- **The odd-part-first grouping**: for `‖q‖ < 1`,
`(q;q)_∞ = ∏'_k ∏'_j (1 - (q^(2k+1))^(2^j))`.

Each inner product is the lacunary Thue–Morse product at the nome
`q^(2k+1)`.  This is the multiplicative counterpart of the additive
residue-class dissection `qPochhammerInfIn_dissection`. -/
theorem qPochhammerInfIn_self_eq_tprod_lacunary {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q =
      ∏' k : ℕ, ∏' j : ℕ, (1 - (q ^ (2 * k + 1)) ^ (2 ^ j)) := by
  have hinner : ∀ k : ℕ, Multipliable fun j : ℕ => 1 - q ^ ((2 * k + 1) * 2 ^ j) := by
    intro k
    have hnorm : ‖q ^ (2 * k + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
    refine (multipliable_one_sub_pow_two_pow_complex hnorm).congr fun j => ?_
    rw [← pow_mul]
  have hsplit : (∏' p : ℕ × ℕ, (1 - q ^ ((2 * p.1 + 1) * 2 ^ p.2))) =
      ∏' k : ℕ, ∏' j : ℕ, (1 - q ^ ((2 * k + 1) * 2 ^ j)) :=
    (multipliable_one_sub_pow_odd_mul_two_pow hq).tprod_prod' hinner
  rw [qPochhammerInfIn_self_eq_tprod_pair q, hsplit]
  exact tprod_congr fun k => tprod_congr fun j => by rw [← pow_mul]

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
