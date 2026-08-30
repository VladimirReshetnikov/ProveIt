import FabiusFunction.LimitConditionNumber
import Mathlib.Tactic.NormNum.BigOperators

/-!
# The cumulant-grid interpolation constant, certified

The exponents volume records that the limiting interpolation
condition number on the cumulant grid `q = 1/4` equals

`(-1/4; 1/4)_∞ / (1/4; 1/4)_∞ = 1.969260353668269431947193696967…`

and recorded, before this module, that the numerical value was not
formalized.  This module formalizes it as far as a kernel-checked
computation reasonably reaches: it proves a **rational enclosure**,
not an evaluation.

## What is actually certified

`qConditionNumberLimit_quarter_enclosure` proves

`1.969260353 < qConditionNumberLimit (1/4) < 1.969260354`,

an interval of width `10⁻⁹` (the underlying bounds are in fact
`1.96926035336…` and `1.96926035366…`, of width `3.1 · 10⁻¹⁰`).  Both
endpoints share the decimal prefix `1.969260353`, so **nine decimals**
of the volume's constant are certified, and no more.  The remaining
twenty digits of the quoted expansion are *not* proved here.  A
coarser cut is recorded as well:
`qConditionNumberLimit_quarter_enclosure_cut14` certifies seven
decimals, `1.9692603`, at the cut whose two prefixes are displayed as
exact rationals in `prefix_self_quarter_eq` and
`prefix_neg_self_quarter_eq`.

## Method: a prefix times a tail

Everything rests on one algebraic fact,
`qPochhammerInf_eq_prefix_mul_tail`: for `0 ≤ q < 1` and any cut `N`,

`(a;q)_∞ = (∏_{j<N} (1 - a q^j)) · (a q^N; q)_∞`.

The tail is *again* a `q`-Pochhammer symbol at the same base, with the
coefficient scaled by `q^N`.  So a tail estimate has to be proved only
once, for a small coefficient `b`, never once per cut.  The four
estimates are `qPochhammerInf_le_one`, `one_sub_le_qPochhammerInf`,
`one_le_qPochhammerInf_neg` and
`qPochhammerInf_neg_mul_one_sub_le_one`.  The first and third need
only `0 ≤ b ≤ 1` and `0 ≤ q < 1`.  The second and fourth are stated
against an abstract deficit budget `E` with `b/(1-q) ≤ E`, and only
the fourth needs `E < 1`.  No threshold on `q` appears anywhere — in
particular *not* `q < 1/2` — so the same lemmas serve any base
`q < 1` once the cut `N` is taken large enough.

Combining the split with the four tail estimates gives the two engine
lemmas `prefix_ratio_le_qConditionNumberLimit` and
`qConditionNumberLimit_le_prefix_ratio`, valid at every base and every
cut:

`Q_N / P_N ≤ (-q;q)_∞/(q;q)_∞ ≤ Q_N / (P_N (1 - E)²)`,

with `P_N = ∏_{j<N}(1 - q·q^j)`, `Q_N = ∏_{j<N}(1 + q·q^j)`.  At
`q = 1/4` the budget is `E = q^{N+1}/(1-q) = 1/(3·4^N)`, so the
enclosure width shrinks by a factor `4` per unit of `N`.  The cut
`N = 16` is used for the headline; `P_16` and `Q_16` are then
rationals over `4^136`, an 82-digit integer, and `norm_num` compares
them without difficulty.

## The index convention, guarded

In this corpus `(q;q)_∞` is `qPochhammerInf q q = ∏_{j≥0}(1 - q^{j+1})`
— the product **starts at `j+1 = 1`**.  An off-by-one in that
convention would silently change the constant, so
`qPochhammerInf_quarter_enclosure` pins the denominator symbol on its
own:

`0.688537537 < (1/4;1/4)_∞ < 0.688537538`.

Under a shifted convention `∏_{j≥0}(1 - q^{j+2})` the same symbol
would equal `0.9180500495…`, and the condition number would be
`1.1815562122…` instead of `1.9692603536…`.  Both lie far outside the
intervals proved here, so the guard rules the shift out rather than
leaving it to prose.

## Main declarations

* `qPochhammerInf_eq_prefix_mul_tail` — **the prefix/tail split**
  `(a;q)_∞ = (∏_{j<N}(1 - a q^j)) · (a q^N;q)_∞`, at a general cut.
* `prefix_self_pos` — the prefix `∏_{j<N}(1 - q·q^j)` is positive.
* `qPochhammerInf_pos_of_lt_one` — `(b;q)_∞ > 0` for `0 ≤ b < 1`.
* `qPochhammerInf_le_one` — `(b;q)_∞ ≤ 1` for `0 ≤ b ≤ 1`.
* `one_sub_le_qPochhammerInf` — `1 - E ≤ (b;q)_∞` whenever the deficit
  budget `b/(1-q)` is at most `E`; the Weierstrass tail bound.
* `one_le_qPochhammerInf_neg` — `1 ≤ (-b;q)_∞` for `0 ≤ b`.
* `qPochhammerInf_neg_mul_one_sub_le_one` — the reciprocal bound
  `(-b;q)_∞ · (1 - E) ≤ 1`, from `(1+x)(1-x) ≤ 1` on finite subsets.
* `qPochhammerInf_self_le_prefix`,
  `prefix_mul_one_sub_le_qPochhammerInf_self` — the two-sided
  enclosure `P_N (1 - E) ≤ (q;q)_∞ ≤ P_N` of the denominator symbol.
* `prefix_ratio_le_qConditionNumberLimit`,
  `qConditionNumberLimit_le_prefix_ratio` — **the enclosure engine**,
  at a general base and a general cut.
* `prefix_self_quarter_eq`, `prefix_neg_self_quarter_eq` — the exact
  rational values of `P_14` and `Q_14` at `q = 1/4`, over `4^105`.
* `qPochhammerInf_quarter_enclosure` — **the index-convention guard**,
  `0.688537537 < (1/4;1/4)_∞ < 0.688537538`.
* `qConditionNumberLimit_quarter_enclosure_cut14` — the cut-`14`
  enclosure `1.9692603 < ρ < 1.9692604`, seven decimals.
* `qConditionNumberLimit_quarter_enclosure` — **the headline**, the
  cut-`16` enclosure `1.969260353 < ρ < 1.969260354`, nine decimals.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-! ## The prefix/tail split -/

/-- **The prefix/tail split of an infinite `q`-Pochhammer symbol.**
For `0 ≤ q < 1` and any cut `N`,

`(a;q)_∞ = (∏_{j<N} (1 - a q^j)) · (a q^N; q)_∞`.

The tail is again a `q`-Pochhammer symbol, at the *same* base `q` and
with the coefficient scaled by `q^N`.  That is what makes the split
iterable, and what lets every tail estimate below be proved once, for
a small coefficient, instead of once per cut. -/
theorem qPochhammerInf_eq_prefix_mul_tail (a : ℝ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (N : ℕ) :
    qPochhammerInf a q =
      (∏ j ∈ Finset.range N, (1 - a * q ^ j)) *
        qPochhammerInf (a * q ^ N) q := by
  have hshift : Multipliable fun i : ℕ => 1 - a * q ^ (i + N) := by
    refine (multipliable_one_sub_mul_pow (a * q ^ N) hq0 hq1).congr
      fun i => ?_
    show 1 - a * q ^ N * q ^ i = 1 - a * q ^ (i + N)
    ring
  have key :
      (∏ i ∈ Finset.range N, (1 - a * q ^ i)) *
          (∏' i : ℕ, (1 - a * q ^ (i + N))) =
        ∏' i : ℕ, (1 - a * q ^ i) :=
    Multipliable.prod_mul_tprod_nat_mul'
      (f := fun j : ℕ => 1 - a * q ^ j) (k := N) hshift
  have htail :
      (∏' i : ℕ, (1 - a * q ^ (i + N))) =
        qPochhammerInf (a * q ^ N) q := by
    rw [qPochhammerInf_eq_tprod]
    refine tprod_congr fun i => ?_
    show 1 - a * q ^ (i + N) = 1 - a * q ^ N * q ^ i
    ring
  calc
    qPochhammerInf a q = ∏' i : ℕ, (1 - a * q ^ i) :=
      qPochhammerInf_eq_tprod a q
    _ = (∏ j ∈ Finset.range N, (1 - a * q ^ j)) *
          (∏' i : ℕ, (1 - a * q ^ (i + N))) := key.symm
    _ = (∏ j ∈ Finset.range N, (1 - a * q ^ j)) *
          qPochhammerInf (a * q ^ N) q := by rw [htail]

/-- The prefix `∏_{j<N} (1 - q·q^j)` of `(q;q)_∞` is strictly
positive, for `0 ≤ q < 1`: every factor is at least `1 - q > 0`. -/
theorem prefix_self_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    0 < ∏ j ∈ Finset.range N, (1 - q * q ^ j) := by
  refine Finset.prod_pos fun j _ => ?_
  show (0 : ℝ) < 1 - q * q ^ j
  have h : q * q ^ j ≤ q :=
    mul_le_of_le_one_right hq0 (pow_le_one₀ hq0 hq1.le)
  linarith

/-! ## The four tail estimates -/

/-- `(b;q)_∞ > 0` whenever `0 ≤ b < 1` and `0 ≤ q < 1`: every factor
`1 - b q^j` is at least `1 - b > 0`.  This is the specialization of
`qPochhammerInf_pos` used on the tails, where the coefficient `b` is a
high power of `q` and therefore tiny. -/
theorem qPochhammerInf_pos_of_lt_one {b q : ℝ} (hb0 : 0 ≤ b)
    (hb1 : b < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < qPochhammerInf b q := by
  refine qPochhammerInf_pos hq0 hq1 fun j => ?_
  have h : b * q ^ j ≤ b :=
    mul_le_of_le_one_right hb0 (pow_le_one₀ hq0 hq1.le)
  linarith

/-- `(b;q)_∞ ≤ 1` for `0 ≤ b ≤ 1` and `0 ≤ q < 1`: every factor lies
in `[0,1]`, so every finite subproduct does, and the bound passes to
the infinite product.  This is the *upper* half of the tail estimate
for the denominator symbol. -/
theorem qPochhammerInf_le_one {b q : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    qPochhammerInf b q ≤ 1 := by
  have hu0 : ∀ j : ℕ, (0 : ℝ) ≤ b * q ^ j :=
    fun j => mul_nonneg hb0 (pow_nonneg hq0 j)
  have hu1 : ∀ j : ℕ, b * q ^ j ≤ 1 := by
    intro j
    have h : b * q ^ j ≤ b :=
      mul_le_of_le_one_right hb0 (pow_le_one₀ hq0 hq1.le)
    linarith
  have hprod : Multipliable fun j : ℕ => 1 - b * q ^ j :=
    multipliable_one_sub_mul_pow b hq0 hq1
  have h : (∏' j : ℕ, (1 - b * q ^ j)) ≤ 1 :=
    tprod_one_sub_le_one (fun j : ℕ => b * q ^ j) hu0 hu1 hprod
  show (∏' j : ℕ, (1 - b * q ^ j)) ≤ 1
  exact h

/-- **The Weierstrass tail bound.**  If `0 ≤ b ≤ 1`, `0 ≤ q < 1` and
the deficit budget `b/(1-q) = ∑_j b q^j` is at most `E`, then

`1 - E ≤ (b;q)_∞`.

The hypothesis is deliberately phrased through an abstract budget `E`
rather than through a threshold on `q`: on a tail with coefficient
`b = q^{N+1}` the budget is small at *every* base `q < 1`, provided
the cut `N` is large enough. -/
theorem one_sub_le_qPochhammerInf {b q E : ℝ} (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbud : b * (1 - q)⁻¹ ≤ E) :
    1 - E ≤ qPochhammerInf b q := by
  have hu0 : ∀ j : ℕ, (0 : ℝ) ≤ b * q ^ j :=
    fun j => mul_nonneg hb0 (pow_nonneg hq0 j)
  have hu1 : ∀ j : ℕ, b * q ^ j ≤ 1 := by
    intro j
    have h : b * q ^ j ≤ b :=
      mul_le_of_le_one_right hb0 (pow_le_one₀ hq0 hq1.le)
    linarith
  have hsum : Summable fun j : ℕ => b * q ^ j :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left b
  have hprod : Multipliable fun j : ℕ => 1 - b * q ^ j :=
    multipliable_one_sub_mul_pow b hq0 hq1
  have hW : 1 - (∑' j : ℕ, b * q ^ j) ≤ ∏' j : ℕ, (1 - b * q ^ j) :=
    one_sub_tsum_le_tprod_one_sub (fun j : ℕ => b * q ^ j) hu0 hu1
      hsum hprod
  have htsum : (∑' j : ℕ, b * q ^ j) = b * (1 - q)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  show 1 - E ≤ ∏' j : ℕ, (1 - b * q ^ j)
  linarith [hW, hbud, htsum.le, htsum.symm.le]

/-- `1 ≤ (-b;q)_∞` for `0 ≤ b` and `0 ≤ q < 1`: every factor of the
product is `1 + b q^j ≥ 1`, so every finite subproduct is at least
one, the empty one included, and the bound passes to the limit with no
eventual-index argument. -/
theorem one_le_qPochhammerInf_neg {b q : ℝ} (hb0 : 0 ≤ b) (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    1 ≤ qPochhammerInf (-b) q := by
  refine le_hasProd_of_le_prod
    (multipliable_one_sub_mul_pow (-b) hq0 hq1).hasProd fun s => ?_
  refine Finset.one_le_prod fun j _ => ?_
  have hnn : (0 : ℝ) ≤ b * q ^ j := mul_nonneg hb0 (pow_nonneg hq0 j)
  show (1 : ℝ) ≤ 1 - -b * q ^ j
  rw [neg_mul, sub_neg_eq_add]
  linarith

/-- **The reciprocal tail bound** `(-b;q)_∞ · (1 - E) ≤ 1`, for
`0 ≤ b ≤ 1`, `0 ≤ q < 1`, deficit budget `b/(1-q) ≤ E` and `E < 1`.

The argument is entirely finite.  On a finite index set `s`, writing
`A = ∏(1 + b q^j)` and `B = ∏(1 - b q^j)`, the identity
`(1+x)(1-x) = 1 - x²` gives `A · B ≤ 1`, while the Weierstrass
inequality gives `B ≥ 1 - ∑ b q^j ≥ 1 - E`; hence
`(1 - E) · A ≤ B · A ≤ 1`, so `A ≤ (1 - E)⁻¹` uniformly in `s`, and
the bound passes to the infinite product.  Stated multiplicatively so
that no division is carried into the arithmetic downstream. -/
theorem qPochhammerInf_neg_mul_one_sub_le_one {b q E : ℝ} (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbud : b * (1 - q)⁻¹ ≤ E) (hE : E < 1) :
    qPochhammerInf (-b) q * (1 - E) ≤ 1 := by
  have hE0 : (0 : ℝ) < 1 - E := by linarith
  have hne : (1 : ℝ) - E ≠ 0 := hE0.ne'
  have hu0 : ∀ j : ℕ, (0 : ℝ) ≤ b * q ^ j :=
    fun j => mul_nonneg hb0 (pow_nonneg hq0 j)
  have hu1 : ∀ j : ℕ, b * q ^ j ≤ 1 := by
    intro j
    have h : b * q ^ j ≤ b :=
      mul_le_of_le_one_right hb0 (pow_le_one₀ hq0 hq1.le)
    linarith
  have hsum : Summable fun j : ℕ => b * q ^ j :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left b
  have htsum : (∑' j : ℕ, b * q ^ j) = b * (1 - q)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hprod : Multipliable fun j : ℕ => 1 - -b * q ^ j :=
    multipliable_one_sub_mul_pow (-b) hq0 hq1
  have hfin : ∀ s : Finset ℕ,
      (∏ j ∈ s, (1 - -b * q ^ j)) ≤ (1 - E)⁻¹ := by
    intro s
    have hA0 : (0 : ℝ) ≤ ∏ j ∈ s, (1 - -b * q ^ j) := by
      refine Finset.prod_nonneg fun j _ => ?_
      show (0 : ℝ) ≤ 1 - -b * q ^ j
      have h := hu0 j
      rw [neg_mul, sub_neg_eq_add]
      linarith
    have hSle : (∑ j ∈ s, b * q ^ j) ≤ ∑' j : ℕ, b * q ^ j :=
      hsum.sum_le_tsum s fun i _ => hu0 i
    have hB : 1 - E ≤ ∏ j ∈ s, (1 - b * q ^ j) := by
      have hW : 1 - (∑ j ∈ s, b * q ^ j) ≤
          ∏ j ∈ s, (1 - b * q ^ j) :=
        one_sub_sum_le_prod_one_sub s (fun j : ℕ => b * q ^ j)
          (fun j _ => hu0 j) (fun j _ => hu1 j)
      linarith [hW, hSle, hbud, htsum.le, htsum.symm.le]
    have hmerge : (∏ j ∈ s, (1 - -b * q ^ j)) *
        (∏ j ∈ s, (1 - b * q ^ j)) =
          ∏ j ∈ s, (1 - (b * q ^ j) ^ 2) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      show (1 - -b * q ^ j) * (1 - b * q ^ j) = 1 - (b * q ^ j) ^ 2
      ring
    have hAB : (∏ j ∈ s, (1 - -b * q ^ j)) *
        (∏ j ∈ s, (1 - b * q ^ j)) ≤ 1 := by
      rw [hmerge]
      exact prod_one_sub_le_one s (fun j : ℕ => (b * q ^ j) ^ 2)
        (fun j _ => pow_nonneg (hu0 j) 2)
        (fun j _ => pow_le_one₀ (hu0 j) (hu1 j))
    have hstep : (1 - E) * (∏ j ∈ s, (1 - -b * q ^ j)) ≤ 1 := by
      have hh : (0 : ℝ) ≤
          ((∏ j ∈ s, (1 - b * q ^ j)) - (1 - E)) *
            (∏ j ∈ s, (1 - -b * q ^ j)) :=
        mul_nonneg (by linarith) hA0
      linarith [hAB, hh]
    have hid : (1 - E)⁻¹ *
        ((1 - E) * ∏ j ∈ s, (1 - -b * q ^ j)) =
          ∏ j ∈ s, (1 - -b * q ^ j) := by
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    have hgoal : (1 - E)⁻¹ *
        ((1 - E) * ∏ j ∈ s, (1 - -b * q ^ j)) ≤ (1 - E)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hstep (inv_pos.2 hE0).le
    rw [hid, mul_one] at hgoal
    exact hgoal
  have hU : qPochhammerInf (-b) q ≤ (1 - E)⁻¹ := by
    show (∏' j : ℕ, (1 - -b * q ^ j)) ≤ (1 - E)⁻¹
    exact hasProd_le_of_prod_le hprod.hasProd hfin
  have h2 := mul_le_mul_of_nonneg_right hU hE0.le
  rw [inv_mul_cancel₀ hne] at h2
  exact h2

/-! ## The denominator symbol between its prefix and a deficit -/

/-- `(q;q)_∞ ≤ ∏_{j<N} (1 - q·q^j)` for `0 ≤ q < 1`: the tail factor
of the split never exceeds one. -/
theorem qPochhammerInf_self_le_prefix {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (N : ℕ) :
    qPochhammerInf q q ≤ ∏ j ∈ Finset.range N, (1 - q * q ^ j) := by
  have hb0 : (0 : ℝ) ≤ q * q ^ N := mul_nonneg hq0 (pow_nonneg hq0 N)
  have hbq : q * q ^ N ≤ q :=
    mul_le_of_le_one_right hq0 (pow_le_one₀ hq0 hq1.le)
  have hb1 : q * q ^ N ≤ 1 := by linarith
  have hT1 : qPochhammerInf (q * q ^ N) q ≤ 1 :=
    qPochhammerInf_le_one hb0 hb1 hq0 hq1
  have hP := prefix_self_pos hq0 hq1 N
  rw [qPochhammerInf_eq_prefix_mul_tail q hq0 hq1 N]
  calc
    (∏ j ∈ Finset.range N, (1 - q * q ^ j)) *
        qPochhammerInf (q * q ^ N) q ≤
          (∏ j ∈ Finset.range N, (1 - q * q ^ j)) * 1 :=
      mul_le_mul_of_nonneg_left hT1 hP.le
    _ = ∏ j ∈ Finset.range N, (1 - q * q ^ j) := mul_one _

/-- `(∏_{j<N} (1 - q·q^j)) · (1 - E) ≤ (q;q)_∞` whenever the tail
budget `q^{N+1}/(1-q)` is at most `E`.  Together with
`qPochhammerInf_self_le_prefix` this brackets the denominator symbol
between `P_N (1 - E)` and `P_N`. -/
theorem prefix_mul_one_sub_le_qPochhammerInf_self {q E : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    (hbud : q * q ^ N * (1 - q)⁻¹ ≤ E) :
    (∏ j ∈ Finset.range N, (1 - q * q ^ j)) * (1 - E) ≤
      qPochhammerInf q q := by
  have hb0 : (0 : ℝ) ≤ q * q ^ N := mul_nonneg hq0 (pow_nonneg hq0 N)
  have hbq : q * q ^ N ≤ q :=
    mul_le_of_le_one_right hq0 (pow_le_one₀ hq0 hq1.le)
  have hb1 : q * q ^ N ≤ 1 := by linarith
  have hTlo : 1 - E ≤ qPochhammerInf (q * q ^ N) q :=
    one_sub_le_qPochhammerInf hb0 hb1 hq0 hq1 hbud
  have hP := prefix_self_pos hq0 hq1 N
  rw [qPochhammerInf_eq_prefix_mul_tail q hq0 hq1 N]
  exact mul_le_mul_of_nonneg_left hTlo hP.le

/-! ## The enclosure engine -/

/-- **Lower engine.**  For `0 ≤ q < 1` and every cut `N`,

`(∏_{j<N}(1 + q·q^j)) / (∏_{j<N}(1 - q·q^j)) ≤ (-q;q)_∞/(q;q)_∞`.

No smallness hypothesis is needed: the numerator tail is at least one
and the denominator tail is at most one, so truncating both can only
decrease the quotient. -/
theorem prefix_ratio_le_qConditionNumberLimit {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (N : ℕ) :
    (∏ j ∈ Finset.range N, (1 - -q * q ^ j)) /
        (∏ j ∈ Finset.range N, (1 - q * q ^ j)) ≤
      qConditionNumberLimit q := by
  have hb0 : (0 : ℝ) ≤ q * q ^ N := mul_nonneg hq0 (pow_nonneg hq0 N)
  have hbq : q * q ^ N ≤ q :=
    mul_le_of_le_one_right hq0 (pow_le_one₀ hq0 hq1.le)
  have hb1 : q * q ^ N ≤ 1 := by linarith
  have hblt : q * q ^ N < 1 := by linarith
  have hP := prefix_self_pos hq0 hq1 N
  have hQ : (1 : ℝ) ≤ ∏ j ∈ Finset.range N, (1 - -q * q ^ j) := by
    refine Finset.one_le_prod fun j _ => ?_
    have hnn : (0 : ℝ) ≤ q * q ^ j := mul_nonneg hq0 (pow_nonneg hq0 j)
    show (1 : ℝ) ≤ 1 - -q * q ^ j
    rw [neg_mul, sub_neg_eq_add]
    linarith
  have hT1 : qPochhammerInf (q * q ^ N) q ≤ 1 :=
    qPochhammerInf_le_one hb0 hb1 hq0 hq1
  have hT0 : 0 < qPochhammerInf (q * q ^ N) q :=
    qPochhammerInf_pos_of_lt_one hb0 hblt hq0 hq1
  have hU1 : (1 : ℝ) ≤ qPochhammerInf (-(q * q ^ N)) q :=
    one_le_qPochhammerInf_neg hb0 hq0 hq1
  have hsp := qPochhammerInf_eq_prefix_mul_tail q hq0 hq1 N
  have hsq := qPochhammerInf_eq_prefix_mul_tail (-q) hq0 hq1 N
  rw [neg_mul q (q ^ N)] at hsq
  have hval : qConditionNumberLimit q =
      ((∏ j ∈ Finset.range N, (1 - -q * q ^ j)) *
          qPochhammerInf (-(q * q ^ N)) q) /
        ((∏ j ∈ Finset.range N, (1 - q * q ^ j)) *
          qPochhammerInf (q * q ^ N) q) := by
    show qPochhammerInf (-q) q / qPochhammerInf q q = _
    rw [hsq, hsp]
  rw [hval, div_le_div_iff₀ hP (mul_pos hP hT0)]
  have hkey : (0 : ℝ) ≤
      (∏ j ∈ Finset.range N, (1 - -q * q ^ j)) *
        (∏ j ∈ Finset.range N, (1 - q * q ^ j)) *
          (qPochhammerInf (-(q * q ^ N)) q -
            qPochhammerInf (q * q ^ N) q) :=
    mul_nonneg (mul_nonneg (by linarith) hP.le) (by linarith)
  linarith [hkey]

/-- **Upper engine.**  For `0 ≤ q < 1`, a cut `N` and a budget `E`
with `q^{N+1}/(1-q) ≤ E < 1`,

`(-q;q)_∞/(q;q)_∞ ≤ Q_N / (P_N (1 - E)²)`,

where `P_N = ∏_{j<N}(1 - q·q^j)` and `Q_N = ∏_{j<N}(1 + q·q^j)`.

One factor of `(1 - E)` comes from the numerator tail through
`qPochhammerInf_neg_mul_one_sub_le_one`, the other from the
denominator tail through `one_sub_le_qPochhammerInf`; that is why the
deficit enters squared. -/
theorem qConditionNumberLimit_le_prefix_ratio {q E : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (N : ℕ) (hbud : q * q ^ N * (1 - q)⁻¹ ≤ E)
    (hE : E < 1) :
    qConditionNumberLimit q ≤
      (∏ j ∈ Finset.range N, (1 - -q * q ^ j)) /
        ((∏ j ∈ Finset.range N, (1 - q * q ^ j)) * (1 - E) ^ 2) := by
  have hE0 : (0 : ℝ) < 1 - E := by linarith
  have hb0 : (0 : ℝ) ≤ q * q ^ N := mul_nonneg hq0 (pow_nonneg hq0 N)
  have hbq : q * q ^ N ≤ q :=
    mul_le_of_le_one_right hq0 (pow_le_one₀ hq0 hq1.le)
  have hb1 : q * q ^ N ≤ 1 := by linarith
  have hP := prefix_self_pos hq0 hq1 N
  have hQ : (1 : ℝ) ≤ ∏ j ∈ Finset.range N, (1 - -q * q ^ j) := by
    refine Finset.one_le_prod fun j _ => ?_
    have hnn : (0 : ℝ) ≤ q * q ^ j := mul_nonneg hq0 (pow_nonneg hq0 j)
    show (1 : ℝ) ≤ 1 - -q * q ^ j
    rw [neg_mul, sub_neg_eq_add]
    linarith
  have hTlo : 1 - E ≤ qPochhammerInf (q * q ^ N) q :=
    one_sub_le_qPochhammerInf hb0 hb1 hq0 hq1 hbud
  have hT0 : 0 < qPochhammerInf (q * q ^ N) q := by linarith
  have hUE : qPochhammerInf (-(q * q ^ N)) q * (1 - E) ≤ 1 :=
    qPochhammerInf_neg_mul_one_sub_le_one hb0 hb1 hq0 hq1 hbud hE
  have hsp := qPochhammerInf_eq_prefix_mul_tail q hq0 hq1 N
  have hsq := qPochhammerInf_eq_prefix_mul_tail (-q) hq0 hq1 N
  rw [neg_mul q (q ^ N)] at hsq
  have hval : qConditionNumberLimit q =
      ((∏ j ∈ Finset.range N, (1 - -q * q ^ j)) *
          qPochhammerInf (-(q * q ^ N)) q) /
        ((∏ j ∈ Finset.range N, (1 - q * q ^ j)) *
          qPochhammerInf (q * q ^ N) q) := by
    show qPochhammerInf (-q) q / qPochhammerInf q q = _
    rw [hsq, hsp]
  rw [hval,
    div_le_div_iff₀ (mul_pos hP hT0) (mul_pos hP (pow_pos hE0 2))]
  have h1 : qPochhammerInf (-(q * q ^ N)) q * (1 - E) * (1 - E) ≤
      1 * (1 - E) :=
    mul_le_mul_of_nonneg_right hUE hE0.le
  have h2 : qPochhammerInf (-(q * q ^ N)) q * (1 - E) ^ 2 ≤
      qPochhammerInf (q * q ^ N) q := by
    linarith [h1, hTlo]
  have hQP : (0 : ℝ) ≤
      (∏ j ∈ Finset.range N, (1 - -q * q ^ j)) *
        (∏ j ∈ Finset.range N, (1 - q * q ^ j)) :=
    mul_nonneg (by linarith) hP.le
  have h3 := mul_le_mul_of_nonneg_left h2 hQP
  linarith [h3]

/-! ## The cumulant grid `q = 1/4` -/

/-- The exact rational value of the cut-`14` prefix of the denominator
symbol at `q = 1/4`, namely `P_14 = ∏_{j=1}^{14} (1 - 4^{-j})`.  The
common denominator is `4^{1+2+⋯+14} = 4^105`, a 64-digit integer; the
numerator is odd, so the fraction is already in lowest terms. -/
theorem prefix_self_quarter_eq :
    (∏ j ∈ Finset.range 14, (1 - (1 / 4 : ℝ) * (1 / 4) ^ j)) =
      1132991656625145684883905396727963355482811684926832351155078125
        / 4 ^ 105 := by
  norm_num [Finset.prod_range_succ]

/-- The exact rational value of the cut-`14` prefix of the numerator
symbol at `q = 1/4`, namely `Q_14 = ∏_{j=1}^{14} (1 + 4^{-j})`, over
the same denominator `4^105`. -/
theorem prefix_neg_self_quarter_eq :
    (∏ j ∈ Finset.range 14, (1 - -(1 / 4 : ℝ) * (1 / 4) ^ j)) =
      2231155544887698126830825546571946372904353170145864154320703125
        / 4 ^ 105 := by
  norm_num [Finset.prod_range_succ]

/-- **Guard against a shifted index convention.**  The denominator
symbol at the cumulant grid satisfies

`0.688537537 < (1/4;1/4)_∞ < 0.688537538`,

nine certified decimals.  In this corpus `(q;q)_∞` is
`qPochhammerInf q q = ∏_{j≥0}(1 - q·q^j) = ∏_{k≥1}(1 - q^k)`, so the
product starts at `k = 1`.  Under the shifted reading
`∏_{k≥2}(1 - q^k)` the same symbol would equal `0.9180500495…`, which
is not in the interval above; the companion condition number would
then be `1.1815562122…` rather than `1.9692603536…`.  The off-by-one
that would otherwise compile silently is therefore excluded by a
theorem rather than by prose.

The bounds come from the cut-`14` bracket
`P_14 (1 - E) ≤ (1/4;1/4)_∞ ≤ P_14` with budget
`E = (1/4)^15/(1 - 1/4) = 1/805306368`. -/
theorem qPochhammerInf_quarter_enclosure :
    0.688537537 < qPochhammerInf (1 / 4 : ℝ) (1 / 4) ∧
      qPochhammerInf (1 / 4 : ℝ) (1 / 4) < 0.688537538 := by
  have hlo := prefix_mul_one_sub_le_qPochhammerInf_self
    (q := (1 / 4 : ℝ)) (E := (1 / 805306368 : ℝ)) (by norm_num)
    (by norm_num) 14 (by norm_num)
  have hhi := qPochhammerInf_self_le_prefix (q := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) 14
  rw [prefix_self_quarter_eq] at hlo hhi
  refine ⟨lt_of_lt_of_le ?_ hlo, lt_of_le_of_lt hhi ?_⟩
  · norm_num
  · norm_num

/-- The cut-`14` enclosure of the cumulant-grid condition number,

`1.9692603 < (-1/4;1/4)_∞/(1/4;1/4)_∞ < 1.9692604`,

**seven** certified decimals, `1.9692603`.  The cut is `N = 14`, so
the prefixes involved are exactly the two rationals over `4^105`
displayed in `prefix_self_quarter_eq` and
`prefix_neg_self_quarter_eq`, which are rewritten in rather than
recomputed, and the budget is `E = 1/805306368`; the underlying
bounds are `1.96926034877…` and `1.96926035366…`.  The sharper
cut-`16` statement is `qConditionNumberLimit_quarter_enclosure`. -/
theorem qConditionNumberLimit_quarter_enclosure_cut14 :
    1.9692603 < qConditionNumberLimit (1 / 4 : ℝ) ∧
      qConditionNumberLimit (1 / 4 : ℝ) < 1.9692604 := by
  have hlo := prefix_ratio_le_qConditionNumberLimit
    (q := (1 / 4 : ℝ)) (by norm_num) (by norm_num) 14
  have hhi := qConditionNumberLimit_le_prefix_ratio
    (q := (1 / 4 : ℝ)) (E := (1 / 805306368 : ℝ)) (by norm_num)
    (by norm_num) 14 (by norm_num) (by norm_num)
  rw [prefix_self_quarter_eq, prefix_neg_self_quarter_eq] at hlo hhi
  refine ⟨lt_of_lt_of_le ?_ hlo, lt_of_le_of_lt hhi ?_⟩
  · norm_num
  · norm_num

/-- **The headline.**  The limiting interpolation condition number on
the cumulant grid `q = 1/4` satisfies

`1.969260353 < (-1/4;1/4)_∞/(1/4;1/4)_∞ < 1.969260354`.

This is an **enclosure**, not an evaluation.  Both endpoints share the
decimal prefix `1.969260353`, so exactly **nine decimals** of the
value `1.969260353668269431947193696967…` quoted by the exponents
volume are certified here; the remaining twenty digits are not
formalized.  The proved bounds are in fact `1.96926035336…` and
`1.96926035366…`, an interval of width `3.1 · 10⁻¹⁰`.

The cut is `N = 16`, with deficit budget
`E = (1/4)^17/(1 - 1/4) = 1/12884901888`; the prefixes `P_16` and
`Q_16` are rationals over `4^136`, an 82-digit integer, so the whole
numeric content is a pair of comparisons between integers of sixty to
eighty decimal digits, discharged by `norm_num` and rechecked by the
kernel — no compiler-trusted evaluation is involved. -/
theorem qConditionNumberLimit_quarter_enclosure :
    1.969260353 < qConditionNumberLimit (1 / 4 : ℝ) ∧
      qConditionNumberLimit (1 / 4 : ℝ) < 1.969260354 := by
  have hlo := prefix_ratio_le_qConditionNumberLimit
    (q := (1 / 4 : ℝ)) (by norm_num) (by norm_num) 16
  have hhi := qConditionNumberLimit_le_prefix_ratio
    (q := (1 / 4 : ℝ)) (E := (1 / 12884901888 : ℝ)) (by norm_num)
    (by norm_num) 16 (by norm_num) (by norm_num)
  refine ⟨lt_of_lt_of_le ?_ hlo, lt_of_le_of_lt hhi ?_⟩
  · norm_num [Finset.prod_range_succ]
  · norm_num [Finset.prod_range_succ]

end Fabius
