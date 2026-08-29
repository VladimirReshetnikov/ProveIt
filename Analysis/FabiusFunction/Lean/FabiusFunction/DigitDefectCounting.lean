import FabiusFunction.WeightedScaleMultiplicity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The dyadic digit defect of a weighted floor series

`WeightedScaleMultiplicity` proves the *floor form* of the cumulative
weighted scale identity: in any additive commutative monoid,
`∑_{m<N} weightedScaleMultiplicity b w (m+1) = ∑_{h<N} (N / b^h) • w h`,
with `N / b^h` the natural (floor) quotient.

This module converts the base-two instance of that finite identity into
a real-analytic one.  Writing `A(1/2) = ∑_h a h · 2^(-h)` for the value
of the weight generating series at `1/2` and
`ρ_a(N) = ∑_h a h · {N / 2^h}` for the weighted dyadic **defect**, the
floor series splits as

`∑_h a h · ⌊N / 2^h⌋ = N · A(1/2) − ρ_a(N)`.

Two things have to be done before that statement even parses.  The
floor side is a *finite* sum in disguise — `⌊N / 2^h⌋ = 0` as soon as
`2^h > N` — so it is bridged to an unconditional `tsum`.  The defect
side does *not* truncate: for large `h` one has `{N / 2^h} = N / 2^h`,
and its summability is exactly the hypothesis
`Summable (fun h ↦ |a h| / 2^h)` which also makes `A(1/2)` converge.
No boundedness of `a` is needed: `{N / 2^h} ≤ N / 2^h` always.

## Main declarations

* `tsum_mul_natCast_div_two_pow_eq_sum_range` — the **truncation
  bridge**: the unconditional sum of `a h · ⌊N / 2^h⌋` is the finite
  sum over any `range M` with `N ≤ M`.
* `fract_natCast_div_two_pow` — the **dyadic fractional part**:
  `{N / 2^h} = (N % 2^h) / 2^h`.
* `mod_two_pow_eq_sum_testBit` and
  `fract_natCast_div_two_pow_eq_sum_range` — the **digit expansion**
  `{N / 2^h} = ∑_{j<h} b_j(N) · 2^j / 2^h` of that fractional part.
* `dyadicWeightValue`, `dyadicDefect` — the two series `A(1/2)` and
  `ρ_a(N)`, together with `dyadicWeightValue_one : A(1/2) = 2` for the
  unit weights.
* `tsum_mul_natCast_div_two_pow` — the **digit-defect identity**
  `∑_h a h · ⌊N / 2^h⌋ = N · A(1/2) − ρ_a(N)`, and its named form
  `tsum_mul_natCast_div_two_pow_defect`.
* `sum_range_weightedScaleMultiplicity_real` — the **real form of the
  cumulative weighted scale identity**: the corpus's monoid-valued
  floor identity at base two, read as `N · A(1/2) − ρ_a(N)`.
* `sum_range_div_two_pow_add_digitSum` — **Legendre's count**
  `∑_{h<M} ⌊N / 2^h⌋ + S₂(N) = 2N`, and its analytic shadow
  `tsum_fract_natCast_div_two_pow`, `dyadicDefect_one`: the *total*
  dyadic defect of `N` is its binary digit sum.  This last pair is the
  regression test fixing the orientation of the main identity.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-! ## Truncation of the floor series -/

/-- Beyond the index `N` every dyadic floor quotient of `N` vanishes. -/
private theorem natDiv_two_pow_eq_zero (N h : ℕ) (hh : N ≤ h) :
    N / 2 ^ h = 0 := by
  refine Nat.div_eq_of_lt ?_
  calc N < 2 ^ N := Nat.lt_two_pow_self
    _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh

/-- **Truncation bridge.**  The weighted floor series has finite
support: summing `a h * ⌊N / 2 ^ h⌋` over all of `ℕ` is the same as
summing it over `range M` for any `M` with `N ≤ M`.

The bound is not optimal — `Nat.log 2 N + 1` would do — but `N` is the
range already used by `sum_range_weightedScaleMultiplicity`. -/
theorem tsum_mul_natCast_div_two_pow_eq_sum_range
    (a : ℕ → ℝ) (N M : ℕ) (hM : N ≤ M) :
    ∑' h : ℕ, a h * ((N / 2 ^ h : ℕ) : ℝ) =
      ∑ h ∈ range M, a h * ((N / 2 ^ h : ℕ) : ℝ) := by
  refine tsum_eq_sum ?_
  intro h hh
  rw [Finset.mem_range, not_lt] at hh
  rw [natDiv_two_pow_eq_zero N h (hM.trans hh), Nat.cast_zero, mul_zero]

/-! ## The fractional part of a dyadic quotient -/

/-- Euclidean division of `N` by `2 ^ h`, read in `ℝ`. -/
private theorem natCast_div_two_pow_split (N h : ℕ) :
    (N : ℝ) / 2 ^ h =
      ((N / 2 ^ h : ℕ) : ℝ) + ((N % 2 ^ h : ℕ) : ℝ) / 2 ^ h := by
  have hne : ((2 : ℝ) ^ h) ≠ 0 := by positivity
  have hN : (2 : ℝ) ^ h * ((N / 2 ^ h : ℕ) : ℝ) +
      ((N % 2 ^ h : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N (2 ^ h)
  rw [← hN, add_div, mul_div_cancel_left₀ _ hne]

/-- **Dyadic fractional part.**  The fractional part of `N / 2 ^ h` is
the normalized dyadic remainder `(N % 2 ^ h) / 2 ^ h`. -/
theorem fract_natCast_div_two_pow (N h : ℕ) :
    Int.fract ((N : ℝ) / 2 ^ h) = ((N % 2 ^ h : ℕ) : ℝ) / 2 ^ h := by
  have hpos : (0 : ℝ) < 2 ^ h := by positivity
  have hlt : ((N % 2 ^ h : ℕ) : ℝ) < 2 ^ h := by
    have h' : N % 2 ^ h < 2 ^ h := Nat.mod_lt N (Nat.two_pow_pos h)
    exact_mod_cast h'
  have hfr : Int.fract (((N % 2 ^ h : ℕ) : ℝ) / 2 ^ h) =
      ((N % 2 ^ h : ℕ) : ℝ) / 2 ^ h :=
    Int.fract_eq_self.mpr
      ⟨by positivity, (div_lt_one hpos).mpr hlt⟩
  rw [natCast_div_two_pow_split N h, Int.fract_natCast_add, hfr]

/-- The dyadic remainder is the sum of the low binary digits of `N`. -/
theorem mod_two_pow_eq_sum_testBit (N h : ℕ) :
    N % 2 ^ h = ∑ j ∈ range h, (N.testBit j).toNat * 2 ^ j := by
  induction h with
  | zero => simp [Nat.mod_one]
  | succ h ih =>
      rw [Nat.mod_pow_succ, ih, Finset.sum_range_succ,
        Nat.toNat_testBit N h]
      ring

/-- **Digit expansion of the dyadic fractional part.**  The `h`-th
dyadic defect of `N` is carried entirely by the binary digits of `N`
below position `h`:  `{N / 2 ^ h} = ∑_{j < h} b_j(N) · 2 ^ j / 2 ^ h`.

This is the substantive half of the digit-defect identity; the
truncation bridge above is the other half. -/
theorem fract_natCast_div_two_pow_eq_sum_range (N h : ℕ) :
    Int.fract ((N : ℝ) / 2 ^ h) =
      ∑ j ∈ range h, ((N.testBit j).toNat : ℝ) * 2 ^ j / 2 ^ h := by
  have hmod : ((N % 2 ^ h : ℕ) : ℝ) =
      ∑ j ∈ range h, ((N.testBit j).toNat : ℝ) * 2 ^ j := by
    rw [mod_two_pow_eq_sum_testBit, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [fract_natCast_div_two_pow N h, hmod, Finset.sum_div]

/-! ## Summability -/

/-- The signed weight series converges as soon as its absolute version
does. -/
private theorem summable_weight
    (a : ℕ → ℝ) (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    Summable fun h : ℕ ↦ a h / 2 ^ h := by
  refine Summable.of_abs ?_
  have habs : ∀ h : ℕ, |a h / (2 : ℝ) ^ h| = |a h| / 2 ^ h := by
    intro h
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ h)]
  simpa only [habs] using ha

/-- The defect series converges under the same hypothesis: the
fractional part never exceeds its argument, so the `h`-th term is
dominated by `N · |a h| / 2 ^ h`. -/
private theorem summable_defect
    (a : ℕ → ℝ) (N : ℕ) (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    Summable fun h : ℕ ↦ a h * Int.fract ((N : ℝ) / 2 ^ h) := by
  have hbig : Summable fun h : ℕ ↦ (N : ℝ) * (|a h| / 2 ^ h) :=
    ha.mul_left (N : ℝ)
  have hkey : ∀ h : ℕ,
      |a h * Int.fract ((N : ℝ) / 2 ^ h)| ≤
        (N : ℝ) * (|a h| / 2 ^ h) := by
    intro h
    have hmod : ((N % 2 ^ h : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.mod_le N (2 ^ h)
    have hle : Int.fract ((N : ℝ) / 2 ^ h) ≤ (N : ℝ) / 2 ^ h := by
      rw [fract_natCast_div_two_pow N h]
      exact div_le_div_of_nonneg_right hmod (by positivity)
    calc |a h * Int.fract ((N : ℝ) / 2 ^ h)|
        = |a h| * Int.fract ((N : ℝ) / 2 ^ h) := by
          rw [abs_mul,
            abs_of_nonneg (Int.fract_nonneg ((N : ℝ) / 2 ^ h))]
      _ ≤ |a h| * ((N : ℝ) / 2 ^ h) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = (N : ℝ) * (|a h| / 2 ^ h) := by ring
  exact Summable.of_abs
    (Summable.of_nonneg_of_le (fun h ↦ abs_nonneg _) hkey hbig)

/-! ## The digit-defect identity -/

/-- The value at `1/2` of the generating series of the weights,
`A(1/2) = ∑_h a h · 2 ^ (-h)`. -/
noncomputable def dyadicWeightValue (a : ℕ → ℝ) : ℝ :=
  ∑' h : ℕ, a h / 2 ^ h

/-- The weighted dyadic digit defect of `N`,
`ρ_a(N) = ∑_h a h · {N / 2 ^ h}`. -/
noncomputable def dyadicDefect (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' h : ℕ, a h * Int.fract ((N : ℝ) / 2 ^ h)

/-- **Digit-defect identity.**  For every real weight sequence with
`∑_h |a h| / 2 ^ h < ∞` the weighted floor series is the linear term
`N · A(1/2)` corrected by the weighted dyadic defect:

`∑_h a h · ⌊N / 2 ^ h⌋ = N · A(1/2) − ρ_a(N)`.

The floor side is a finite sum in disguise; the two series on the right
are genuinely infinite, and both converge under the single hypothesis
`ha`.  No boundedness of `a` is required. -/
theorem tsum_mul_natCast_div_two_pow
    (a : ℕ → ℝ) (N : ℕ) (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    ∑' h : ℕ, a h * ((N / 2 ^ h : ℕ) : ℝ) =
      (N : ℝ) * (∑' h : ℕ, a h / 2 ^ h) -
        ∑' h : ℕ, a h * Int.fract ((N : ℝ) / 2 ^ h) := by
  have ha' := summable_weight a ha
  have hd := summable_defect a N ha
  have hpoint : ∀ h : ℕ, a h * ((N / 2 ^ h : ℕ) : ℝ) =
      (N : ℝ) * (a h / 2 ^ h) -
        a h * Int.fract ((N : ℝ) / 2 ^ h) := by
    intro h
    have hq : ((N / 2 ^ h : ℕ) : ℝ) =
        (N : ℝ) / 2 ^ h - Int.fract ((N : ℝ) / 2 ^ h) := by
      rw [fract_natCast_div_two_pow N h,
        natCast_div_two_pow_split N h]
      ring
    rw [hq]
    ring
  calc ∑' h : ℕ, a h * ((N / 2 ^ h : ℕ) : ℝ)
      = ∑' h : ℕ, ((N : ℝ) * (a h / 2 ^ h) -
          a h * Int.fract ((N : ℝ) / 2 ^ h)) := tsum_congr hpoint
    _ = (∑' h : ℕ, (N : ℝ) * (a h / 2 ^ h)) -
          ∑' h : ℕ, a h * Int.fract ((N : ℝ) / 2 ^ h) :=
        (ha'.mul_left (N : ℝ)).tsum_sub hd
    _ = (N : ℝ) * (∑' h : ℕ, a h / 2 ^ h) -
          ∑' h : ℕ, a h * Int.fract ((N : ℝ) / 2 ^ h) := by
        rw [tsum_mul_left]

/-- The digit-defect identity in the named notation `A(1/2)` and
`ρ_a(N)`. -/
theorem tsum_mul_natCast_div_two_pow_defect
    (a : ℕ → ℝ) (N : ℕ) (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    ∑' h : ℕ, a h * ((N / 2 ^ h : ℕ) : ℝ) =
      (N : ℝ) * dyadicWeightValue a - dyadicDefect a N :=
  tsum_mul_natCast_div_two_pow a N ha

/-- **Real form of the cumulative weighted scale identity.**  Summing
the base-two weighted scale multiplicities of `1, …, N` — the corpus's
monoid-valued statement `sum_range_weightedScaleMultiplicity`, read in
`ℝ` — produces the linear term `N · A(1/2)` minus the dyadic defect. -/
theorem sum_range_weightedScaleMultiplicity_real
    (a : ℕ → ℝ) (N : ℕ) (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    ∑ m ∈ range N, weightedScaleMultiplicity 2 a (m + 1) =
      (N : ℝ) * dyadicWeightValue a - dyadicDefect a N := by
  calc ∑ m ∈ range N, weightedScaleMultiplicity 2 a (m + 1)
      = ∑ h ∈ range N, (N / 2 ^ h) • a h :=
        sum_range_weightedScaleMultiplicity 2 N a (by norm_num)
    _ = ∑ h ∈ range N, a h * ((N / 2 ^ h : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun h _ ↦ ?_
        rw [nsmul_eq_mul]
        ring
    _ = ∑' h : ℕ, a h * ((N / 2 ^ h : ℕ) : ℝ) :=
        (tsum_mul_natCast_div_two_pow_eq_sum_range a N N
          le_rfl).symm
    _ = (N : ℝ) * dyadicWeightValue a - dyadicDefect a N :=
        tsum_mul_natCast_div_two_pow_defect a N ha

/-! ## Legendre's count as a regression test -/

private theorem one_div_two_pow_eq (h : ℕ) :
    (1 : ℝ) / 2 ^ h = ((1 : ℝ) / 2) ^ h := by
  rw [div_pow, one_pow]

private theorem summable_one_div_two_pow :
    Summable fun h : ℕ ↦ (1 : ℝ) / 2 ^ h := by
  simpa only [one_div_two_pow_eq] using summable_geometric_two

private theorem tsum_one_div_two_pow :
    ∑' h : ℕ, (1 : ℝ) / 2 ^ h = 2 := by
  simpa only [one_div_two_pow_eq] using tsum_geometric_two

/-- The unit weight sequence has generating value `A(1/2) = 2`. -/
theorem dyadicWeightValue_one :
    dyadicWeightValue (fun _ ↦ (1 : ℝ)) = 2 :=
  tsum_one_div_two_pow

/-- **Legendre's count.**  Over any range containing every nonvanishing
layer, the dyadic floor quotients of `N` and the binary digit sum of
`N` partition `2N`:  `∑_{h<M} ⌊N / 2 ^ h⌋ + S₂(N) = 2N`.

The additive form avoids truncated subtraction; it is Legendre's
formula `v₂(N!) = N − S₂(N)` with the `h = 0` layer `⌊N⌋ = N` added
back. -/
theorem sum_range_div_two_pow_add_digitSum (N M : ℕ)
    (hM : Nat.log 2 N < M) :
    (∑ h ∈ range M, N / 2 ^ h) + (Nat.digits 2 N).sum = 2 * N := by
  have hM0 : 0 < M := by omega
  have hsplit : ∑ h ∈ range M, N / 2 ^ h =
      N / 2 ^ 0 + ∑ h ∈ Finset.Ico 1 M, N / 2 ^ h :=
    Finset.sum_range_eq_add_Ico _ hM0
  have hleg : padicValNat 2 (Nat.factorial N) =
      ∑ i ∈ Finset.Ico 1 M, N / 2 ^ i := padicValNat_factorial hM
  have hdig : padicValNat 2 (Nat.factorial N) =
      N - (Nat.digits 2 N).sum := by
    have h2 := sub_one_mul_padicValNat_factorial (p := 2) N
    simpa only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] using h2
  have hle : (Nat.digits 2 N).sum ≤ N := Nat.digit_sum_le 2 N
  rw [hsplit, ← hleg, pow_zero, Nat.div_one]
  omega

/-- **The total dyadic defect is the binary digit sum.**  Taking every
weight equal to `1`, the digit-defect identity reads
`∑_h ⌊N / 2 ^ h⌋ = 2N − S₂(N)`, so the unweighted defect series
evaluates to `S₂(N)`:

`∑_h {N / 2 ^ h} = S₂(N)`.

This is the regression test for the orientation of
`tsum_mul_natCast_div_two_pow`: the sign of the defect term is fixed by
Legendre's classical count. -/
theorem tsum_fract_natCast_div_two_pow (N : ℕ) :
    ∑' h : ℕ, Int.fract ((N : ℝ) / 2 ^ h) =
      ((Nat.digits 2 N).sum : ℝ) := by
  have hone : Summable fun h : ℕ ↦ |(1 : ℝ)| / 2 ^ h := by
    simpa only [abs_one] using summable_one_div_two_pow
  have hmain :=
    tsum_mul_natCast_div_two_pow (fun _ ↦ (1 : ℝ)) N hone
  simp only [one_mul] at hmain
  rw [tsum_one_div_two_pow] at hmain
  have hbridge : ∑' h : ℕ, ((N / 2 ^ h : ℕ) : ℝ) =
      ∑ h ∈ range (N + 1), ((N / 2 ^ h : ℕ) : ℝ) := by
    have hb := tsum_mul_natCast_div_two_pow_eq_sum_range
      (fun _ ↦ (1 : ℝ)) N (N + 1) (Nat.le_succ N)
    simpa only [one_mul] using hb
  have hnat : (∑ h ∈ range (N + 1), N / 2 ^ h) +
      (Nat.digits 2 N).sum = 2 * N :=
    sum_range_div_two_pow_add_digitSum N (N + 1)
      (by have := Nat.log_le_self 2 N; omega)
  have hcast : (∑ h ∈ range (N + 1), ((N / 2 ^ h : ℕ) : ℝ)) +
      ((Nat.digits 2 N).sum : ℝ) = 2 * (N : ℝ) := by
    exact_mod_cast hnat
  rw [hbridge] at hmain
  linarith

/-- The unit-weight defect: `ρ₁(N) = S₂(N)`. -/
theorem dyadicDefect_one (N : ℕ) :
    dyadicDefect (fun _ ↦ (1 : ℝ)) N =
      ((Nat.digits 2 N).sum : ℝ) := by
  show ∑' h : ℕ, (1 : ℝ) * Int.fract ((N : ℝ) / 2 ^ h) =
    ((Nat.digits 2 N).sum : ℝ)
  simp only [one_mul]
  exact tsum_fract_natCast_div_two_pow N

end Fabius
