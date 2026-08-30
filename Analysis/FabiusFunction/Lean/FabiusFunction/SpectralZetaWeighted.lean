import FabiusFunction.WeightedScaleMultiplicity
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The weighted spectral zeta series

For a weight sequence `a : ℕ → ℝ` the exponents volume defines the
spectral zeta function of the base-`b` scale filtration by

`Z_a(s) = ∑_{n ≥ 1} m_a(n) · n^(-s) = ζ(s) · A(b^(-s))`,

where `m_a(n) = ∑_{h ≤ ν_b(n)} a_h` is the weighted scale multiplicity
(`weightedScaleMultiplicity`, formalized in full generality in
`FabiusFunction.WeightedScaleMultiplicity`) and `A(q) = ∑_h a_h q^h`.

This module proves that identity over the reals, for a real exponent
`s > 1` and an arbitrary base `b > 1`, in the self-contained form

`∑'_n m_a(n+1)·(n+1)^(-s)
   = (∑'_n (n+1)^(-s)) · ∑'_h a_h·b^(-h·s)`,

both factors being `tsum`s of explicitly given families.

## The mechanism

For `n ≥ 1`, `m_a(n)` is the sum of `a h` over the heights `h` with
`b^h ∣ n`.  So the series is the double family

`spectralZetaCell b a s h n = if b^h ∣ n then a h · n^(-s) else 0`

summed over `ℕ × ℕ`, and the identity is Fubini for that family.  The
two iterated sums are:

* over `h` at fixed `n` — a *finite* sum for `n ≥ 1`, the fibre
  `{h : b^h ∣ n}`, which is exactly what `m_a(n)` adds up;
* over `n` at fixed `h` — the multiples of `b^h`, reindexed by
  `k ↦ b^h · k`, which contributes `a_h · b^(-h·s)` times the bare
  power series.

The index map `(h, k) ↦ b^h · k` is *not* injective: its fibre over
`n ≥ 1` is `{h : b^h ∣ n}`, of size `ν_b(n) + 1`, and that
non-injectivity is precisely what produces `m_a`.  At `n = 0` every
scale divides, but `0^(-s) = 0` kills the whole row, so both sides
vanish and that case is split off separately.

The regrouping is therefore done with
`Summable.tsum_comm` on `ℕ × ℕ`, whose summability comes from
`summable_prod_of_nonneg`: nonnegativity is what reduces the
two-dimensional summability to the two one-dimensional conditions,
and that summability is what licenses the exchange.  Only the
*inner* reindexing,
over the multiples of a fixed `b^h`, is injective, and that step uses
`Function.Injective.tsum_eq` (`tsum_ite_dvd`).

## Hypotheses, and why each is needed

* `1 < b` — the base; `b = 0, 1` degenerate.
* `1 < s` — convergence of `∑ n^(-s)`.
* `0 ≤ a h` — nonnegativity, so that `summable_prod_of_nonneg`
  reduces summability of the double family to the two column
  conditions.
* `Summable (fun h ↦ a h * b^(-h·s))` — *not* automatic: `a` may grow
  arbitrarily fast, so the layer series `A(b^(-s))` must be assumed
  convergent.  It is stated, never silently used.

## Honest scope

This is the **arithmetic half** of the volume's theorem
`p1:thm:zero-zeta`: it proves `p1:eq:zeta-a` in full for real
`s > 1` and arbitrary base `b > 1`, with the zeta factor left as its
own `p`-series.  The other half, the canonical product
`p1:eq:canonical-a`, is independent of it.

The volume recorded both as proved and listed the **general-`a`**
product and this zeta identity as its two unformalized items.  The
`a ≡ 1` case of the product is `Fabius.rvachevFourierProduct_eq_canonical`
in `SincCanonicalProduct.lean`, and the general-`a` case is
`Fabius.generalizedRvachevProduct_eq_canonical` in
`FabiusFunction.GeneralizedCanonicalForm` — so both items are now
closed, and with the order of vanishing on top of the product
(`FabiusFunction.GeneralizedRvachevEntire`).  The zeta identity never
needed the product in any case: it is a
pure Dirichlet-series rearrangement about `m_a`, and `m_a` is
already formalized — at arbitrary base and in an arbitrary additive
commutative monoid, as the volume itself notes.

The Riemann zeta *function* does not appear.  The first factor is left
as its own series `∑'_n (n+1)^(-s)`; identifying it with `riemannZeta s`
would need the complex `LSeries` machinery and a real-to-complex bridge,
which buys nothing here.  Nothing in this module is conditional on that
identification.

## Main declarations

* `spectralZetaCell` — the cell `if b^h ∣ n then a h · n^(-s) else 0`
  of the double family.
* `spectralZetaCell_nonneg` — cells are nonnegative.
* `natCast_scale_rpow` — `(b^h·k)^(-s) = b^(-h·s) · k^(-s)`.
* `rpow_neg_natCast_mul` — `b^(-h·s) = (b^(-s))^h`, the `A(q)` form.
* `tsum_ite_dvd` — reindexing a series supported on the multiples of
  `q` by the multiplier (the injective half of the regrouping).
* `summable_ite_dvd` — the same reindexing for summability.
* `summable_spectralZetaCell_col` — each column is summable.
* `tsum_spectralZetaCell_col` — **the column sum**, `= a h · b^(-h·s) ·
  ∑' k^(-s)`.
* `tsum_spectralZetaCell_row` — **the fibre sum**, `= m_a(n) · n^(-s)`.
* `summable_uncurry_spectralZetaCell` — **summability of the double
  family** over `ℕ × ℕ`.
* `summable_weightedScaleMultiplicity_rpow` — the Dirichlet series of
  `m_a` converges.
* `tsum_weightedScaleMultiplicity_rpow` — the identity indexed by all
  of `ℕ` (the index `0` contributes nothing).
* `tsum_weightedScaleMultiplicity_succ_rpow` — **the headline**, the
  spectral zeta identity as a Dirichlet series over `n ≥ 1`.
* `tsum_weightedScaleMultiplicity_succ_rpow_two` — the dyadic case
  `b = 2`, the volume's `p1:eq:zeta-a`.
* `weightedScaleMultiplicity_one` — unit weights give `ν_b(n) + 1`.
* `tsum_padicValNat_succ_rpow` — **the guard** at `a ≡ 1`:
  `∑ (ν_b(n)+1)·n^(-s) = (∑ n^(-s)) · (1 - b^(-s))⁻¹`.
* `tsum_padicValNat_succ_rpow_two` — the guard at `b = 2`.

The guard was checked numerically before being stated: at `b = 2` the
left side, summed directly to `2·10^7`, agrees with `ζ(s)/(1-2^(-s))`
to the predicted truncation error — fifteen digits at `s = 3`, and at
`s = 2` the discrepancy is `1.0000·10^(-7)` against the predicted tail
`2N^(1-s)/(s-1) = 10^(-7)`.  This pins the `ν_b(n) + 1` convention.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- One cell of the double family behind the spectral zeta series: the
weight `a h` attached to the index `n`, retained exactly when the scale
`b ^ h` divides `n`. -/
noncomputable def spectralZetaCell (b : ℕ) (a : ℕ → ℝ) (s : ℝ)
    (h n : ℕ) : ℝ :=
  if b ^ h ∣ n then a h * (n : ℝ) ^ (-s) else 0

/-- Every cell is nonnegative as soon as the weights are. -/
theorem spectralZetaCell_nonneg (b : ℕ) (a : ℕ → ℝ) (s : ℝ)
    (ha : ∀ h, 0 ≤ a h) (h n : ℕ) :
    0 ≤ spectralZetaCell b a s h n := by
  unfold spectralZetaCell
  split_ifs
  · exact mul_nonneg (ha h) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · exact le_rfl

/-- The real power of a scaled index factors:
`(b^h · k)^(-s) = b^(-h·s) · k^(-s)`. -/
theorem natCast_scale_rpow (b : ℕ) (s : ℝ) (h k : ℕ) :
    ((b ^ h * k : ℕ) : ℝ) ^ (-s)
      = (b : ℝ) ^ (-(h : ℝ) * s) * (k : ℝ) ^ (-s) := by
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hbn : (0 : ℝ) ≤ (b : ℝ) ^ h := pow_nonneg hb0 h
  have hexp : ((b : ℝ) ^ h) ^ (-s) = (b : ℝ) ^ (-(h : ℝ) * s) := by
    rw [← Real.rpow_natCast (b : ℝ) h, ← Real.rpow_mul hb0,
      show (h : ℝ) * -s = -(h : ℝ) * s from by ring]
  rw [Nat.cast_mul, Nat.cast_pow,
    Real.mul_rpow hbn (Nat.cast_nonneg k), hexp]

/-- The layer weight in exponential form: `b^(-h·s) = (b^(-s))^h`, so
that `∑' h, a h * b^(-h·s)` really is `A(q)` at `q = b^(-s)`. -/
theorem rpow_neg_natCast_mul (b : ℕ) (s : ℝ) (h : ℕ) :
    (b : ℝ) ^ (-(h : ℝ) * s) = ((b : ℝ) ^ (-s)) ^ h := by
  rw [show -(h : ℝ) * s = -s * (h : ℝ) from by ring,
    Real.rpow_mul (Nat.cast_nonneg b), Real.rpow_natCast]

/-- **The injective half of the regrouping.**  A series supported on
the multiples of `q` reindexes as a series over all multipliers. -/
theorem tsum_ite_dvd (u : ℕ → ℝ) (q : ℕ) (hq : 0 < q) :
    ∑' n : ℕ, (if q ∣ n then u n else 0) = ∑' k : ℕ, u (q * k) := by
  have hinj : Function.Injective (fun k : ℕ => q * k) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left hq hxy
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => q * k),
      (if q ∣ n then u n else 0) = 0 := by
    intro n hn
    refine if_neg ?_
    rintro ⟨k, rfl⟩
    exact hn (Set.mem_range.mpr ⟨k, rfl⟩)
  have hsupp :
      Function.support (fun n : ℕ => if q ∣ n then u n else 0)
        ⊆ Set.range (fun k : ℕ => q * k) :=
    Function.support_subset_iff'.mpr hzero
  have key : ∑' k : ℕ, (if q ∣ q * k then u (q * k) else 0)
      = ∑' n : ℕ, (if q ∣ n then u n else 0) :=
    hinj.tsum_eq (f := fun n : ℕ => if q ∣ n then u n else 0) hsupp
  calc ∑' n : ℕ, (if q ∣ n then u n else 0)
      = ∑' k : ℕ, (if q ∣ q * k then u (q * k) else 0) := key.symm
    _ = ∑' k : ℕ, u (q * k) := by
        refine tsum_congr fun k => ?_
        show (if q ∣ q * k then u (q * k) else 0) = u (q * k)
        rw [if_pos (Nat.dvd_mul_right q k)]

/-- Summability transfers along the same reindexing. -/
theorem summable_ite_dvd (u : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (hu : Summable fun k : ℕ => u (q * k)) :
    Summable fun n : ℕ => (if q ∣ n then u n else 0) := by
  have hinj : Function.Injective (fun k : ℕ => q * k) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left hq hxy
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => q * k),
      (if q ∣ n then u n else 0) = 0 := by
    intro n hn
    refine if_neg ?_
    rintro ⟨k, rfl⟩
    exact hn (Set.mem_range.mpr ⟨k, rfl⟩)
  have hiff :
      (Summable fun k : ℕ => (if q ∣ q * k then u (q * k) else 0))
        ↔ Summable fun n : ℕ => (if q ∣ n then u n else 0) :=
    hinj.summable_iff
      (f := fun n : ℕ => if q ∣ n then u n else 0) hzero
  refine hiff.mp (hu.congr ?_)
  intro k
  show u (q * k) = if q ∣ q * k then u (q * k) else 0
  rw [if_pos (Nat.dvd_mul_right q k)]

/-- Each column of the double family is summable: it is a constant
multiple of a convergent `p`-series. -/
theorem summable_spectralZetaCell_col (b : ℕ) (a : ℕ → ℝ) (s : ℝ)
    (hb : 1 < b) (hs : 1 < s) (h : ℕ) :
    Summable fun n : ℕ => spectralZetaCell b a s h n := by
  have hq : 0 < b ^ h := pow_pos (by omega) h
  have hZ : Summable fun n : ℕ => (n : ℝ) ^ (-s) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hcol : Summable fun k : ℕ =>
      a h * (b : ℝ) ^ (-(h : ℝ) * s) * (k : ℝ) ^ (-s) := hZ.mul_left _
  have hcol' : Summable fun k : ℕ =>
      a h * ((b ^ h * k : ℕ) : ℝ) ^ (-s) := by
    refine hcol.congr ?_
    intro k
    show a h * (b : ℝ) ^ (-(h : ℝ) * s) * (k : ℝ) ^ (-s)
        = a h * ((b ^ h * k : ℕ) : ℝ) ^ (-s)
    rw [natCast_scale_rpow b s h k, mul_assoc]
  have hres := summable_ite_dvd (fun n : ℕ => a h * (n : ℝ) ^ (-s))
    (b ^ h) hq hcol'
  refine hres.congr ?_
  intro n
  show (if b ^ h ∣ n then a h * (n : ℝ) ^ (-s) else 0)
      = spectralZetaCell b a s h n
  rfl

/-- **The column sum.**  Summing one layer over all indices gives the
layer weight `a h · b^(-h·s)` times the bare power series. -/
theorem tsum_spectralZetaCell_col (b : ℕ) (a : ℕ → ℝ) (s : ℝ)
    (hb : 1 < b) (hs : 1 < s) (h : ℕ) :
    (∑' n : ℕ, spectralZetaCell b a s h n)
      = a h * (b : ℝ) ^ (-(h : ℝ) * s)
        * ∑' k : ℕ, (k : ℝ) ^ (-s) := by
  have hq : 0 < b ^ h := pow_pos (by omega) h
  have hZ : Summable fun n : ℕ => (n : ℝ) ^ (-s) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc (∑' n : ℕ, spectralZetaCell b a s h n)
      = ∑' n : ℕ, (if b ^ h ∣ n then a h * (n : ℝ) ^ (-s) else 0) :=
        tsum_congr fun n => rfl
    _ = ∑' k : ℕ, a h * ((b ^ h * k : ℕ) : ℝ) ^ (-s) :=
        tsum_ite_dvd (fun n : ℕ => a h * (n : ℝ) ^ (-s)) (b ^ h) hq
    _ = ∑' k : ℕ,
          (a h * (b : ℝ) ^ (-(h : ℝ) * s) * (k : ℝ) ^ (-s)) := by
        refine tsum_congr fun k => ?_
        show a h * ((b ^ h * k : ℕ) : ℝ) ^ (-s)
            = a h * (b : ℝ) ^ (-(h : ℝ) * s) * (k : ℝ) ^ (-s)
        rw [natCast_scale_rpow b s h k, mul_assoc]
    _ = a h * (b : ℝ) ^ (-(h : ℝ) * s)
          * ∑' k : ℕ, (k : ℝ) ^ (-s) :=
        hZ.tsum_mul_left (a h * (b : ℝ) ^ (-(h : ℝ) * s))

/-- **The fibre sum.**  The heights whose scale divides `n` are exactly
the ones the weighted scale multiplicity adds up, so summing the cells
over all heights recovers `m_a(n) · n^(-s)`.

This is the step where the non-injectivity of `(h, k) ↦ b^h · k`
becomes visible: the fibre over `n` has `ν_b(n) + 1` elements. -/
theorem tsum_spectralZetaCell_row (b : ℕ) (a : ℕ → ℝ) (s : ℝ)
    (hb : 1 < b) (hs : 1 < s) (n : ℕ) :
    (∑' h : ℕ, spectralZetaCell b a s h n)
      = weightedScaleMultiplicity b a n * (n : ℝ) ^ (-s) := by
  have hb1 : b ≠ 1 := by omega
  have hsneg : (-s : ℝ) < 0 := by linarith
  have hz : ((0 : ℕ) : ℝ) ^ (-s) = 0 := by
    rw [Nat.cast_zero]
    exact Real.zero_rpow hsneg.ne
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hcell : ∀ h : ℕ, spectralZetaCell b a s h 0 = 0 := by
      intro h
      unfold spectralZetaCell
      rw [if_pos (Nat.dvd_zero (b ^ h)), hz, mul_zero]
    calc (∑' h : ℕ, spectralZetaCell b a s h 0)
        = ∑' _h : ℕ, (0 : ℝ) := tsum_congr hcell
      _ = 0 := tsum_zero
      _ = weightedScaleMultiplicity b a 0
            * ((0 : ℕ) : ℝ) ^ (-s) := by rw [hz, mul_zero]
  · have hn : n ≠ 0 := by omega
    have hsupp : ∀ h ∉ range n, spectralZetaCell b a s h n = 0 := by
      intro h hh
      rw [Finset.mem_range, not_lt] at hh
      unfold spectralZetaCell
      refine if_neg ?_
      intro hd
      rw [Nat.pow_dvd_iff_le_padicValNat hb1 hn] at hd
      have hlt := Nat.padicValNat_lt_self (p := b) hn
      omega
    calc (∑' h : ℕ, spectralZetaCell b a s h n)
        = ∑ h ∈ range n, spectralZetaCell b a s h n :=
          tsum_eq_sum hsupp
      _ = ∑ h ∈ (range n).filter (fun h => b ^ h ∣ n),
            a h * (n : ℝ) ^ (-s) := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun h _ => rfl
      _ = (∑ h ∈ (range n).filter (fun h => b ^ h ∣ n), a h)
            * (n : ℝ) ^ (-s) := by rw [Finset.sum_mul]
      _ = weightedScaleMultiplicity b a n * (n : ℝ) ^ (-s) := by
          rw [weightedScaleMultiplicity_eq_sum_filter_pow_dvd
            b a n hb1 hn]

/-- **Summability of the double family** over `ℕ × ℕ`.  Nonnegativity
turns summability into the two one-dimensional conditions: every column
converges (that is `1 < s`) and the column sums converge (that is the
hypothesis `hA` on the layer weights). -/
theorem summable_uncurry_spectralZetaCell (b : ℕ) (a : ℕ → ℝ) (s : ℝ)
    (hb : 1 < b) (hs : 1 < s) (ha : ∀ h, 0 ≤ a h)
    (hA : Summable fun h : ℕ => a h * (b : ℝ) ^ (-(h : ℝ) * s)) :
    Summable (Function.uncurry (spectralZetaCell b a s)) := by
  have hnn : (0 : ℕ × ℕ → ℝ)
      ≤ Function.uncurry (spectralZetaCell b a s) := by
    intro p
    exact spectralZetaCell_nonneg b a s ha p.1 p.2
  rw [summable_prod_of_nonneg hnn]
  refine ⟨?_, ?_⟩
  · intro h
    exact summable_spectralZetaCell_col b a s hb hs h
  · refine (hA.mul_right (∑' k : ℕ, (k : ℝ) ^ (-s))).congr ?_
    intro h
    show a h * (b : ℝ) ^ (-(h : ℝ) * s)
        * (∑' k : ℕ, (k : ℝ) ^ (-s))
        = ∑' n : ℕ, spectralZetaCell b a s h n
    exact (tsum_spectralZetaCell_col b a s hb hs h).symm

/-- The Dirichlet series of the weighted scale multiplicity converges
under the same three hypotheses. -/
theorem summable_weightedScaleMultiplicity_rpow (b : ℕ) (a : ℕ → ℝ)
    (s : ℝ) (hb : 1 < b) (hs : 1 < s) (ha : ∀ h, 0 ≤ a h)
    (hA : Summable fun h : ℕ => a h * (b : ℝ) ^ (-(h : ℝ) * s)) :
    Summable fun n : ℕ =>
      weightedScaleMultiplicity b a n * (n : ℝ) ^ (-s) := by
  have hunc := summable_uncurry_spectralZetaCell b a s hb hs ha hA
  refine (hunc.prod_symm.prod).congr ?_
  intro n
  show (∑' h : ℕ, spectralZetaCell b a s h n)
      = weightedScaleMultiplicity b a n * (n : ℝ) ^ (-s)
  exact tsum_spectralZetaCell_row b a s hb hs n

/-- **The spectral zeta identity**, indexed by all of `ℕ`.  The index
`0` contributes nothing on either side, because `0 ^ (-s) = 0`. -/
theorem tsum_weightedScaleMultiplicity_rpow (b : ℕ) (a : ℕ → ℝ)
    (s : ℝ) (hb : 1 < b) (hs : 1 < s) (ha : ∀ h, 0 ≤ a h)
    (hA : Summable fun h : ℕ => a h * (b : ℝ) ^ (-(h : ℝ) * s)) :
    (∑' n : ℕ, weightedScaleMultiplicity b a n * (n : ℝ) ^ (-s))
      = (∑' n : ℕ, (n : ℝ) ^ (-s))
        * ∑' h : ℕ, a h * (b : ℝ) ^ (-(h : ℝ) * s) := by
  have hunc := summable_uncurry_spectralZetaCell b a s hb hs ha hA
  have hcomm : (∑' n : ℕ, ∑' h : ℕ, spectralZetaCell b a s h n)
      = ∑' h : ℕ, ∑' n : ℕ, spectralZetaCell b a s h n :=
    Summable.tsum_comm hunc
  calc (∑' n : ℕ, weightedScaleMultiplicity b a n * (n : ℝ) ^ (-s))
      = ∑' n : ℕ, ∑' h : ℕ, spectralZetaCell b a s h n :=
        tsum_congr fun n =>
          (tsum_spectralZetaCell_row b a s hb hs n).symm
    _ = ∑' h : ℕ, ∑' n : ℕ, spectralZetaCell b a s h n := hcomm
    _ = ∑' h : ℕ, (a h * (b : ℝ) ^ (-(h : ℝ) * s)
          * ∑' k : ℕ, (k : ℝ) ^ (-s)) :=
        tsum_congr fun h => tsum_spectralZetaCell_col b a s hb hs h
    _ = (∑' h : ℕ, a h * (b : ℝ) ^ (-(h : ℝ) * s))
          * ∑' k : ℕ, (k : ℝ) ^ (-s) :=
        hA.tsum_mul_right (∑' k : ℕ, (k : ℝ) ^ (-s))
    _ = (∑' n : ℕ, (n : ℝ) ^ (-s))
          * ∑' h : ℕ, a h * (b : ℝ) ^ (-(h : ℝ) * s) := mul_comm _ _

/-- **The spectral zeta identity** (`p1:eq:zeta-a`, arithmetic half),
as a Dirichlet series over `n ≥ 1`:

`∑'_n m_a(n+1)·(n+1)^(-s)
   = (∑'_n (n+1)^(-s)) · ∑'_h a_h·b^(-h·s)`.

The first factor is the `p`-series that equals `ζ(s)`; it is left as
its own `tsum`, so the statement is self-contained. -/
theorem tsum_weightedScaleMultiplicity_succ_rpow (b : ℕ) (a : ℕ → ℝ)
    (s : ℝ) (hb : 1 < b) (hs : 1 < s) (ha : ∀ h, 0 ≤ a h)
    (hA : Summable fun h : ℕ => a h * (b : ℝ) ^ (-(h : ℝ) * s)) :
    (∑' n : ℕ, weightedScaleMultiplicity b a (n + 1)
        * ((n : ℝ) + 1) ^ (-s))
      = (∑' n : ℕ, ((n : ℝ) + 1) ^ (-s))
        * ∑' h : ℕ, a h * (b : ℝ) ^ (-(h : ℝ) * s) := by
  have hsneg : (-s : ℝ) < 0 := by linarith
  have hz : ((0 : ℕ) : ℝ) ^ (-s) = 0 := by
    rw [Nat.cast_zero]
    exact Real.zero_rpow hsneg.ne
  have hcast : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    intro n
    rw [Nat.cast_add, Nat.cast_one]
  have hZs : Summable fun n : ℕ => (n : ℝ) ^ (-s) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hMs :=
    summable_weightedScaleMultiplicity_rpow b a s hb hs ha hA
  have hZ0 : (∑' n : ℕ, (n : ℝ) ^ (-s))
      = ((0 : ℕ) : ℝ) ^ (-s)
        + ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-s) :=
    hZs.tsum_eq_zero_add
  have hM0 :
      (∑' n : ℕ, weightedScaleMultiplicity b a n * (n : ℝ) ^ (-s))
        = weightedScaleMultiplicity b a 0 * ((0 : ℕ) : ℝ) ^ (-s)
          + ∑' n : ℕ, weightedScaleMultiplicity b a (n + 1)
              * ((n + 1 : ℕ) : ℝ) ^ (-s) :=
    hMs.tsum_eq_zero_add
  rw [hz, mul_zero, zero_add] at hM0
  rw [hz, zero_add] at hZ0
  have hZ' : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-s))
      = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-s) := by
    refine tsum_congr fun n => ?_
    show ((n : ℝ) + 1) ^ (-s) = ((n + 1 : ℕ) : ℝ) ^ (-s)
    rw [hcast n]
  have hM' : (∑' n : ℕ, weightedScaleMultiplicity b a (n + 1)
        * ((n : ℝ) + 1) ^ (-s))
      = ∑' n : ℕ, weightedScaleMultiplicity b a (n + 1)
          * ((n + 1 : ℕ) : ℝ) ^ (-s) := by
    refine tsum_congr fun n => ?_
    show weightedScaleMultiplicity b a (n + 1) * ((n : ℝ) + 1) ^ (-s)
        = weightedScaleMultiplicity b a (n + 1)
          * ((n + 1 : ℕ) : ℝ) ^ (-s)
    rw [hcast n]
  rw [hM', hZ', ← hM0, ← hZ0]
  exact tsum_weightedScaleMultiplicity_rpow b a s hb hs ha hA

/-- The dyadic case `b = 2` of the spectral zeta identity: the volume's
`p1:eq:zeta-a` for the Fabius scale filtration. -/
theorem tsum_weightedScaleMultiplicity_succ_rpow_two (a : ℕ → ℝ)
    (s : ℝ) (hs : 1 < s) (ha : ∀ h, 0 ≤ a h)
    (hA : Summable fun h : ℕ => a h * (2 : ℝ) ^ (-(h : ℝ) * s)) :
    (∑' n : ℕ, weightedScaleMultiplicity 2 a (n + 1)
        * ((n : ℝ) + 1) ^ (-s))
      = (∑' n : ℕ, ((n : ℝ) + 1) ^ (-s))
        * ∑' h : ℕ, a h * (2 : ℝ) ^ (-(h : ℝ) * s) := by
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have hA' : Summable fun h : ℕ =>
      a h * ((2 : ℕ) : ℝ) ^ (-(h : ℝ) * s) := by
    rw [h2]
    exact hA
  have key := tsum_weightedScaleMultiplicity_succ_rpow 2 a s
    (by norm_num) hs ha hA'
  rw [h2] at key
  exact key

/-- Unit weights turn the weighted scale multiplicity into the plain
layer count `ν_b(n) + 1`. -/
theorem weightedScaleMultiplicity_one (b n : ℕ) :
    weightedScaleMultiplicity b (fun _ => (1 : ℝ)) n
      = (padicValNat b n : ℝ) + 1 := by
  have hexp : weightedScaleMultiplicity b (fun _ => (1 : ℝ)) n
      = ∑ _h ∈ range (padicValNat b n + 1), (1 : ℝ) := rfl
  rw [hexp, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Nat.cast_add, Nat.cast_one]

/-- **The guard at unit weights.**  With `a ≡ 1` the multiplicity is
`ν_b(n) + 1` and the layer series is the geometric series `1/(1-q)` at
`q = b^(-s)`, so the identity reads

`∑'_n (ν_b(n+1)+1)·(n+1)^(-s) = (∑'_n (n+1)^(-s)) · (1 - b^(-s))⁻¹`,

i.e. `ζ(s)/(1 - b^(-s))`.  An off-by-one in the `ν_b(n) + 1` convention
would break this, which is why it is stated. -/
theorem tsum_padicValNat_succ_rpow (b : ℕ) (s : ℝ) (hb : 1 < b)
    (hs : 1 < s) :
    (∑' n : ℕ,
        ((padicValNat b (n + 1) : ℝ) + 1) * ((n : ℝ) + 1) ^ (-s))
      = (∑' n : ℕ, ((n : ℝ) + 1) ^ (-s))
        * (1 - (b : ℝ) ^ (-s))⁻¹ := by
  have hbR : (1 : ℝ) < (b : ℝ) := Nat.one_lt_cast.mpr hb
  have hr0 : (0 : ℝ) ≤ (b : ℝ) ^ (-s) :=
    Real.rpow_nonneg (Nat.cast_nonneg b) _
  have hr1 : (b : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hbR (by linarith)
  have hterm : ∀ h : ℕ, (1 : ℝ) * (b : ℝ) ^ (-(h : ℝ) * s)
      = ((b : ℝ) ^ (-s)) ^ h := by
    intro h
    rw [one_mul, rpow_neg_natCast_mul]
  have hAsum :
      Summable fun h : ℕ => (1 : ℝ) * (b : ℝ) ^ (-(h : ℝ) * s) := by
    refine (summable_geometric_of_lt_one hr0 hr1).congr ?_
    intro h
    exact (hterm h).symm
  have hA : (∑' h : ℕ, (1 : ℝ) * (b : ℝ) ^ (-(h : ℝ) * s))
      = (1 - (b : ℝ) ^ (-s))⁻¹ := by
    rw [tsum_congr hterm]
    exact tsum_geometric_of_lt_one hr0 hr1
  have key : (∑' n : ℕ,
        weightedScaleMultiplicity b (fun _ => (1 : ℝ)) (n + 1)
          * ((n : ℝ) + 1) ^ (-s))
      = (∑' n : ℕ, ((n : ℝ) + 1) ^ (-s))
        * ∑' h : ℕ, (1 : ℝ) * (b : ℝ) ^ (-(h : ℝ) * s) :=
    tsum_weightedScaleMultiplicity_succ_rpow b (fun _ => (1 : ℝ)) s
      hb hs (fun _ => zero_le_one) hAsum
  rw [hA] at key
  rw [← key]
  refine tsum_congr fun n => ?_
  show ((padicValNat b (n + 1) : ℝ) + 1) * ((n : ℝ) + 1) ^ (-s)
      = weightedScaleMultiplicity b (fun _ => (1 : ℝ)) (n + 1)
        * ((n : ℝ) + 1) ^ (-s)
  rw [weightedScaleMultiplicity_one]

/-- The guard in the dyadic case `b = 2`:
`∑'_n (ν₂(n+1)+1)·(n+1)^(-s) = (∑'_n (n+1)^(-s))·(1 - 2^(-s))⁻¹`.

Numerically, at `s = 2` both sides are
`2π²/9 = 2.1932454224643019…` and at `s = 3` both are
`ζ(3)·8/7 = 1.3737793178966791833…`. -/
theorem tsum_padicValNat_succ_rpow_two (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ,
        ((padicValNat 2 (n + 1) : ℝ) + 1) * ((n : ℝ) + 1) ^ (-s))
      = (∑' n : ℕ, ((n : ℝ) + 1) ^ (-s))
        * (1 - (2 : ℝ) ^ (-s))⁻¹ := by
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have key := tsum_padicValNat_succ_rpow 2 s (by norm_num) hs
  rw [h2] at key
  exact key

end Fabius
