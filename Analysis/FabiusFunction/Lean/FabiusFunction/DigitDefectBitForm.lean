import FabiusFunction.DigitDefectCounting
import Mathlib.Data.Nat.Bitwise
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The bit form of the weighted dyadic digit defect

`DigitDefectCounting` proves the *defect form* of the cumulative
weighted scale identity: under the single hypothesis
`Summable (fun h ↦ |a h| / 2 ^ h)`,

`∑_h a h · ⌊N / 2 ^ h⌋ = N · A(1/2) − ρ_a(N)`,

with `A(1/2) = ∑_h a h · 2 ^ (-h)` (`dyadicWeightValue`) and
`ρ_a(N) = ∑_h a h · {N / 2 ^ h}` (`dyadicDefect`).  It also proves the
per-scale digit expansion `{N / 2 ^ h} = ∑_{j < h} b_j(N) · 2 ^ (j−h)`.
This module performs the exchange of summation that turns the defect
into a **sum over the binary digits of `N`**.

Substituting the digit expansion and collecting the coefficient of
`b_j(N)` produces the *tail weight*

`τ_j(a) = ∑_{h > j} a h · 2 ^ (j−h) = ∑_{k ≥ 1} a (j+k) · 2 ^ (−k)`,

so that `ρ_a(N) = ∑_j b_j(N) · τ_j(a)` and hence

`∑_h a h · ⌊N / 2 ^ h⌋ = N · A(1/2) − ∑_j b_j(N) · τ_j(a)`.

The exchange is *not* a Fubini theorem on the triangle
`{(j,h) : j < h}`.  Only finitely many digits of `N` are nonzero, so
after replacing `range h` by a fixed window `range M` with `N < 2 ^ M`
— legitimate because the added terms carry either a vanishing digit or
a vanishing layer weight — the inner sum is a *finite* sum over an
index set that does not depend on `h`.  What remains is the exchange of
a `tsum` with a `Finset.sum`, which needs exactly one summability
hypothesis per digit; absolute convergence of `∑_h |a h| 2 ^ (−h)`
supplies it, since the layer weight `2 ^ (j−h)` is at most `2 ^ j`
times `2 ^ (−h)`.

## Main declarations

* `dyadicTailWeight` — the **tail weight** `τ_j(a)`, defined as the
  series `∑_k a (k + (j+1)) / 2 ^ (k+1)`, and
  `dyadicTailWeight_eq_tsum_succ`, which exhibits it in the printed
  form `∑_{k ≥ 1} a (j + k) · 2 ^ (−k)`.
* `summable_dyadicTailWeight_terms` — the tail weight is **well
  defined**: its defining series converges under the same hypothesis
  `Summable (fun h ↦ |a h| / 2 ^ h)` that the defect form uses.
* `dyadicTailWeight_one` — `τ_j(1) = 1` for the unit weights;
  `dyadicTailWeight_congr` — the tail weight at `j` reads `a` only
  from index `j + 1` upwards; and `dyadicTailWeight_succ` — the
  **halving recursion** `τ_j(a) = (a (j+1) + τ_{j+1}(a)) / 2`, which
  pins the index convention.
* `dyadicDefect_eq_sum_range_testBit` — the **bit form on a window**:
  for `N < 2 ^ M`, `ρ_a(N) = ∑_{j < M} b_j(N) · τ_j(a)`, and
  `dyadicDefect_eq_tsum_testBit`, its unconditional `tsum` form.
* `tsum_mul_natCast_div_two_pow_bit` and
  `sum_range_weightedScaleMultiplicity_bit` — the **bit form of the
  weighted scale identity**, `∑_h a h · ⌊N / 2 ^ h⌋` and the cumulative
  multiplicity sum read as `N · A(1/2) − ∑_j b_j(N) · τ_j(a)`.
* `tsum_testBit_eq_digitSum` — the **consistency check**: specializing
  the bit form to `a ≡ 1`, where `τ_j = 1`, and comparing with
  `dyadicDefect_one` (Legendre's count, already in the corpus) yields
  `∑_j b_j(N) = S₂(N)`.  That identity is true independently of this
  module, so deriving it through the new tail weight and the new
  exchange makes the kernel check both against the audited
  unit-weight case.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-! ## The layer weight of one digit at one scale -/

/-- The weight with which digit `j` of `N` enters the scale-`h`
fractional part `{N / 2 ^ h}`: it is `2 ^ (j−h)` when the digit lies
below the scale, and `0` otherwise. -/
private noncomputable def dyadicLayer (j h : ℕ) : ℝ :=
  if j < h then (2 : ℝ) ^ j / 2 ^ h else 0

private theorem dyadicLayer_of_lt {j h : ℕ} (hjh : j < h) :
    dyadicLayer j h = (2 : ℝ) ^ j / 2 ^ h := by
  show (if j < h then (2 : ℝ) ^ j / 2 ^ h else 0) = (2 : ℝ) ^ j / 2 ^ h
  exact if_pos hjh

private theorem dyadicLayer_of_le {j h : ℕ} (hjh : h ≤ j) :
    dyadicLayer j h = 0 := by
  show (if j < h then (2 : ℝ) ^ j / 2 ^ h else 0) = 0
  exact if_neg (by omega)

/-- Shifting the scale past the digit turns the layer weight into a
plain geometric factor: `a (k+j+1) · 2 ^ (j − (k+j+1)) = a (k+j+1) /
2 ^ (k+1)`. -/
private theorem layer_shift (a : ℕ → ℝ) (j k : ℕ) :
    a (k + (j + 1)) * dyadicLayer j (k + (j + 1)) =
      a (k + (j + 1)) / 2 ^ (k + 1) := by
  have hidx : k + (j + 1) = j + (k + 1) := by omega
  have h3 : ((2 : ℝ) ^ (k + (j + 1))) = 2 ^ j * 2 ^ (k + 1) := by
    rw [hidx]
    exact pow_add 2 j (k + 1)
  have h1 : ((2 : ℝ) ^ j * 2 ^ (k + 1)) ≠ 0 := by positivity
  have h2 : ((2 : ℝ) ^ (k + 1)) ≠ 0 := by positivity
  have hlt : j < k + (j + 1) := by omega
  rw [dyadicLayer_of_lt hlt, h3, ← mul_div_assoc,
    div_eq_div_iff h1 h2]
  ring

/-- Each digit layer of a summable weight sequence is itself summable:
the `h`-th term is dominated by `2 ^ j · |a h| / 2 ^ h`. -/
private theorem summable_layer (a : ℕ → ℝ) (j : ℕ)
    (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    Summable fun h : ℕ ↦ a h * dyadicLayer j h := by
  have hbig : Summable fun h : ℕ ↦ (2 : ℝ) ^ j * (|a h| / 2 ^ h) :=
    ha.mul_left ((2 : ℝ) ^ j)
  have hkey : ∀ h : ℕ, |a h * dyadicLayer j h| ≤
      (2 : ℝ) ^ j * (|a h| / 2 ^ h) := by
    intro h
    rcases lt_or_ge j h with hjh | hjh
    · rw [dyadicLayer_of_lt hjh, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ j / 2 ^ h)]
      exact le_of_eq (by ring)
    · rw [dyadicLayer_of_le hjh, mul_zero, abs_zero]
      positivity
  exact Summable.of_abs
    (Summable.of_nonneg_of_le (fun h ↦ abs_nonneg _) hkey hbig)

/-! ## The tail weight -/

/-- The **tail weight** attached to binary digit `j`,
`τ_j(a) = ∑_{k ≥ 1} a (j + k) · 2 ^ (−k)`.

It is the coefficient of `b_j(N)` in the dyadic defect: the digit `j`
of `N` contributes `2 ^ (j−h)` to the scale-`h` fractional part for
every scale `h > j`, and those contributions are collected here. -/
noncomputable def dyadicTailWeight (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑' k : ℕ, a (k + (j + 1)) / 2 ^ (k + 1)

/-- **The tail weight is well defined.**  Its defining series converges
under the same hypothesis that makes `A(1/2)` and the defect converge;
no boundedness of `a` is required. -/
theorem summable_dyadicTailWeight_terms (a : ℕ → ℝ) (j : ℕ)
    (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    Summable fun k : ℕ ↦ a (k + (j + 1)) / 2 ^ (k + 1) := by
  have hshift : Summable fun k : ℕ ↦
      a (k + (j + 1)) * dyadicLayer j (k + (j + 1)) :=
    (summable_nat_add_iff
      (f := fun h : ℕ ↦ a h * dyadicLayer j h) (j + 1)).mpr
      (summable_layer a j ha)
  exact hshift.congr fun k ↦ layer_shift a j k

/-- **The tail weight in printed form.**  Reindexing the defining
series by `k ↦ k + 1` exhibits `τ_j(a)` as `∑_{k ≥ 1} a (j+k) 2 ^ (−k)`:
the summand at `k` is the weight of scale `j + k`, discounted by
`2 ^ (−k)`. -/
theorem dyadicTailWeight_eq_tsum_succ (a : ℕ → ℝ) (j : ℕ) :
    dyadicTailWeight a j =
      ∑' k : ℕ, a (j + (k + 1)) / 2 ^ (k + 1) := by
  have hdef : dyadicTailWeight a j =
      ∑' k : ℕ, a (k + (j + 1)) / 2 ^ (k + 1) := rfl
  rw [hdef]
  refine tsum_congr fun k ↦ ?_
  have hidx : k + (j + 1) = j + (k + 1) := by omega
  rw [hidx]

/-- **The tail weight at `j` depends only on the weights above `j`.**
Two weight sequences agreeing from index `j + 1` on have the same tail
weight at `j`.  No summability is needed: if the series diverge, both
`tsum`s are `0`. -/
theorem dyadicTailWeight_congr (a b : ℕ → ℝ) (j : ℕ)
    (hab : ∀ k : ℕ, a (k + (j + 1)) = b (k + (j + 1))) :
    dyadicTailWeight a j = dyadicTailWeight b j := by
  have hda : dyadicTailWeight a j =
      ∑' k : ℕ, a (k + (j + 1)) / 2 ^ (k + 1) := rfl
  have hdb : dyadicTailWeight b j =
      ∑' k : ℕ, b (k + (j + 1)) / 2 ^ (k + 1) := rfl
  rw [hda, hdb]
  exact tsum_congr fun k ↦ by rw [hab k]

/-- **Halving recursion for the tail weight.**
`τ_j(a) = (a (j+1) + τ_{j+1}(a)) / 2`.

This is the computational form of the definition, and it pins the index
convention: the value at `j` is built from `a (j+1)` and the value at
`j + 1`.  Together with `dyadicTailWeight_congr` it says that `τ_j(a)`
reads `a` only from index `j + 1` upwards. -/
theorem dyadicTailWeight_succ (a : ℕ → ℝ) (j : ℕ)
    (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    dyadicTailWeight a j =
      (a (j + 1) + dyadicTailWeight a (j + 1)) / 2 := by
  have hdefj : dyadicTailWeight a j =
      ∑' k : ℕ, a (k + (j + 1)) / 2 ^ (k + 1) := rfl
  have hdefs : dyadicTailWeight a (j + 1) =
      ∑' k : ℕ, a (k + (j + 1 + 1)) / 2 ^ (k + 1) := rfl
  have hs := summable_dyadicTailWeight_terms a j ha
  have hhead :
      a (0 + (j + 1)) / (2 : ℝ) ^ (0 + 1) = a (j + 1) / 2 := by
    norm_num
  have htail : ∀ k : ℕ,
      a (k + 1 + (j + 1)) / (2 : ℝ) ^ (k + 1 + 1) =
        (1 / 2 : ℝ) * (a (k + (j + 1 + 1)) / 2 ^ (k + 1)) := by
    intro k
    have hpow : ((2 : ℝ) ^ (k + 1 + 1)) = 2 ^ (k + 1) * 2 :=
      pow_succ 2 (k + 1)
    have hidx : k + 1 + (j + 1) = k + (j + 1 + 1) := by omega
    rw [hidx, hpow, ← div_div]
    ring
  rw [hdefj, hdefs]
  calc ∑' k : ℕ, a (k + (j + 1)) / 2 ^ (k + 1)
      = a (0 + (j + 1)) / 2 ^ (0 + 1) +
          ∑' k : ℕ, a (k + 1 + (j + 1)) / 2 ^ (k + 1 + 1) :=
        hs.tsum_eq_zero_add
    _ = (a (j + 1) +
          ∑' k : ℕ, a (k + (j + 1 + 1)) / 2 ^ (k + 1)) / 2 := by
        rw [hhead, tsum_congr htail, tsum_mul_left]
        ring

/-! ## The unit weights -/

private theorem tsum_one_div_two_pow_succ :
    ∑' k : ℕ, (1 : ℝ) / 2 ^ (k + 1) = 1 := by
  have hterm : ∀ k : ℕ,
      (1 : ℝ) / 2 ^ (k + 1) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
    intro k
    have hpow : ((1 : ℝ) / 2) ^ (k + 1) = 1 / 2 ^ (k + 1) := by
      rw [div_pow, one_pow]
    rw [← hpow, pow_succ]
    exact mul_comm _ _
  calc ∑' k : ℕ, (1 : ℝ) / 2 ^ (k + 1)
      = ∑' k : ℕ, (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := tsum_congr hterm
    _ = (1 / 2 : ℝ) * ∑' k : ℕ, (1 / 2 : ℝ) ^ k := tsum_mul_left
    _ = 1 := by rw [tsum_geometric_two]; norm_num

private theorem summable_abs_one :
    Summable fun h : ℕ ↦ |(1 : ℝ)| / 2 ^ h := by
  have hterm : ∀ h : ℕ, ((1 : ℝ) / 2) ^ h = |(1 : ℝ)| / 2 ^ h := by
    intro h
    rw [div_pow, one_pow, abs_one]
  exact summable_geometric_two.congr hterm

/-- **Unit tail weight.**  Every digit of `N` carries weight `1` when
all scale weights are `1`:  `τ_j(1) = ∑_{k ≥ 1} 2 ^ (−k) = 1`. -/
theorem dyadicTailWeight_one (j : ℕ) :
    dyadicTailWeight (fun _ ↦ (1 : ℝ)) j = 1 := by
  show ∑' k : ℕ, (1 : ℝ) / 2 ^ (k + 1) = 1
  exact tsum_one_div_two_pow_succ

/-! ## The digit expansion on a fixed window -/

/-- **Digit expansion on a window independent of the scale.**  If
`N < 2 ^ M` then, for *every* scale `h`,
`{N / 2 ^ h} = ∑_{j < M} b_j(N) · 2 ^ (j−h)`, the layer weight being
zero unless `j < h`.

`fract_natCast_div_two_pow_eq_sum_range` gives the same expansion over
`range h`; the point here is that the index set no longer depends on
`h`.  Digits at or above `M` vanish because `N < 2 ^ M`, and layers at
or above `h` carry weight zero, so both truncations may be enlarged to
the common window `range (M + h)`. -/
private theorem fract_eq_sum_window (N M h : ℕ) (hN : N < 2 ^ M) :
    Int.fract ((N : ℝ) / 2 ^ h) =
      ∑ j ∈ range M, ((N.testBit j).toNat : ℝ) * dyadicLayer j h := by
  have hzero : ∀ j : ℕ, M ≤ j →
      ((N.testBit j).toNat : ℝ) * dyadicLayer j h = 0 := by
    intro j hj
    have hb : N.testBit j = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) hj))
    rw [hb, Bool.toNat_false, Nat.cast_zero, zero_mul]
  have h1 : ∑ j ∈ range M,
      ((N.testBit j).toNat : ℝ) * dyadicLayer j h =
      ∑ j ∈ range (M + h),
        ((N.testBit j).toNat : ℝ) * dyadicLayer j h := by
    refine Finset.sum_subset
      (Finset.range_subset_range.mpr (Nat.le_add_right M h)) ?_
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    exact hzero j hj
  have hstep : ∑ j ∈ range h,
      ((N.testBit j).toNat : ℝ) * 2 ^ j / 2 ^ h =
      ∑ j ∈ range h,
        ((N.testBit j).toNat : ℝ) * dyadicLayer j h := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [dyadicLayer_of_lt hj, mul_div_assoc]
  have h2 : ∑ j ∈ range h,
      ((N.testBit j).toNat : ℝ) * 2 ^ j / 2 ^ h =
      ∑ j ∈ range (M + h),
        ((N.testBit j).toNat : ℝ) * dyadicLayer j h := by
    rw [hstep]
    refine Finset.sum_subset
      (Finset.range_subset_range.mpr (Nat.le_add_left h M)) ?_
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [dyadicLayer_of_le hj, mul_zero]
  rw [fract_natCast_div_two_pow_eq_sum_range N h]
  exact h2.trans h1.symm

/-- The scale series of a single digit sums to that digit's tail
weight:  `∑_h a h · 2 ^ (j−h) = τ_j(a)`, the terms with `h ≤ j`
vanishing. -/
private theorem tsum_layer (a : ℕ → ℝ) (j : ℕ)
    (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    ∑' h : ℕ, a h * dyadicLayer j h = dyadicTailWeight a j := by
  have hs := summable_layer a j ha
  have hzero : ∑ i ∈ range (j + 1), a i * dyadicLayer j i = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    have hle : i ≤ j := by omega
    rw [dyadicLayer_of_le hle, mul_zero]
  calc ∑' h : ℕ, a h * dyadicLayer j h
      = (∑ i ∈ range (j + 1), a i * dyadicLayer j i) +
          ∑' k : ℕ, a (k + (j + 1)) * dyadicLayer j (k + (j + 1)) :=
        (hs.sum_add_tsum_nat_add (j + 1)).symm
    _ = ∑' k : ℕ, a (k + (j + 1)) / 2 ^ (k + 1) := by
        rw [hzero, zero_add]
        exact tsum_congr fun k ↦ layer_shift a j k
    _ = dyadicTailWeight a j := rfl

/-! ## The bit form -/

/-- **Bit form of the dyadic defect, on a window.**  For `N < 2 ^ M`,

`ρ_a(N) = ∑_{j < M} b_j(N) · τ_j(a)`.

The hypothesis `ha` is the one already used for the defect form; no
boundedness of `a` is needed.  The proof exchanges the scale `tsum`
with the finite digit sum supplied by `fract_eq_sum_window`, which is
legitimate because each digit's scale series converges separately. -/
theorem dyadicDefect_eq_sum_range_testBit
    (a : ℕ → ℝ) (N M : ℕ) (ha : Summable fun h ↦ |a h| / 2 ^ h)
    (hN : N < 2 ^ M) :
    dyadicDefect a N =
      ∑ j ∈ range M,
        ((N.testBit j).toNat : ℝ) * dyadicTailWeight a j := by
  have hdef : dyadicDefect a N =
      ∑' h : ℕ, a h * Int.fract ((N : ℝ) / 2 ^ h) := rfl
  have hpoint : ∀ h : ℕ, a h * Int.fract ((N : ℝ) / 2 ^ h) =
      ∑ j ∈ range M,
        ((N.testBit j).toNat : ℝ) * (a h * dyadicLayer j h) := by
    intro h
    rw [fract_eq_sum_window N M h hN, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hsum : ∀ j ∈ range M, Summable fun h : ℕ ↦
      ((N.testBit j).toNat : ℝ) * (a h * dyadicLayer j h) :=
    fun j _ ↦ (summable_layer a j ha).mul_left _
  rw [hdef]
  calc ∑' h : ℕ, a h * Int.fract ((N : ℝ) / 2 ^ h)
      = ∑' h : ℕ, ∑ j ∈ range M,
          ((N.testBit j).toNat : ℝ) * (a h * dyadicLayer j h) :=
        tsum_congr hpoint
    _ = ∑ j ∈ range M, ∑' h : ℕ,
          ((N.testBit j).toNat : ℝ) * (a h * dyadicLayer j h) :=
        Summable.tsum_finsetSum hsum
    _ = ∑ j ∈ range M,
          ((N.testBit j).toNat : ℝ) * dyadicTailWeight a j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [tsum_mul_left, tsum_layer a j ha]

/-- **Bit form of the dyadic defect.**  Unconditionally over all
digits,

`ρ_a(N) = ∑_j b_j(N) · τ_j(a)`.

The series on the right has finite support: `b_j(N) = 0` once
`2 ^ j > N`. -/
theorem dyadicDefect_eq_tsum_testBit
    (a : ℕ → ℝ) (N : ℕ) (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    dyadicDefect a N =
      ∑' j : ℕ, ((N.testBit j).toNat : ℝ) * dyadicTailWeight a j := by
  have hlt : N < 2 ^ N := Nat.lt_two_pow_self
  have hfin : ∑' j : ℕ,
      ((N.testBit j).toNat : ℝ) * dyadicTailWeight a j =
      ∑ j ∈ range N,
        ((N.testBit j).toNat : ℝ) * dyadicTailWeight a j := by
    refine tsum_eq_sum ?_
    intro j hj
    rw [Finset.mem_range, not_lt] at hj
    have hb : N.testBit j = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hj))
    rw [hb, Bool.toNat_false, Nat.cast_zero, zero_mul]
  rw [hfin]
  exact dyadicDefect_eq_sum_range_testBit a N N ha hlt

/-- **Bit form of the weighted floor series.**

`∑_h a h · ⌊N / 2 ^ h⌋ = N · A(1/2) − ∑_j b_j(N) · τ_j(a)`.

This is the digit-defect identity of `DigitDefectCounting` with the
defect resolved into its binary digits: the linear term is a transform
of `a` evaluated at `1/2`, and the correction is a weighted binary
digit sum, the ordinary digit sum being the case `a ≡ 1`. -/
theorem tsum_mul_natCast_div_two_pow_bit
    (a : ℕ → ℝ) (N : ℕ) (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    ∑' h : ℕ, a h * ((N / 2 ^ h : ℕ) : ℝ) =
      (N : ℝ) * dyadicWeightValue a -
        ∑' j : ℕ,
          ((N.testBit j).toNat : ℝ) * dyadicTailWeight a j := by
  rw [tsum_mul_natCast_div_two_pow_defect a N ha,
    dyadicDefect_eq_tsum_testBit a N ha]

/-- The same identity over a window `range M` with `N < 2 ^ M`, where
the digit sum is visibly finite. -/
theorem tsum_mul_natCast_div_two_pow_bit_range
    (a : ℕ → ℝ) (N M : ℕ) (ha : Summable fun h ↦ |a h| / 2 ^ h)
    (hN : N < 2 ^ M) :
    ∑' h : ℕ, a h * ((N / 2 ^ h : ℕ) : ℝ) =
      (N : ℝ) * dyadicWeightValue a -
        ∑ j ∈ range M,
          ((N.testBit j).toNat : ℝ) * dyadicTailWeight a j := by
  rw [tsum_mul_natCast_div_two_pow_defect a N ha,
    dyadicDefect_eq_sum_range_testBit a N M ha hN]

/-- **Bit form of the cumulative weighted scale identity.**  Summing
the base-two weighted scale multiplicities of `1, …, N` gives the
linear term `N · A(1/2)` corrected by a weighted binary digit sum:

`∑_{m < N} weightedScaleMultiplicity 2 a (m+1)
   = N · A(1/2) − ∑_j b_j(N) · τ_j(a)`.

This is the reading of `sum_range_weightedScaleMultiplicity_real` in
which the ordinary binary weight of `N` is replaced by the weighted
suffix transform `τ` of the scale weights. -/
theorem sum_range_weightedScaleMultiplicity_bit
    (a : ℕ → ℝ) (N : ℕ) (ha : Summable fun h ↦ |a h| / 2 ^ h) :
    ∑ m ∈ range N, weightedScaleMultiplicity 2 a (m + 1) =
      (N : ℝ) * dyadicWeightValue a -
        ∑' j : ℕ,
          ((N.testBit j).toNat : ℝ) * dyadicTailWeight a j := by
  rw [sum_range_weightedScaleMultiplicity_real a N ha,
    dyadicDefect_eq_tsum_testBit a N ha]

/-! ## Consistency with Legendre's count -/

/-- **Consistency check.**  At the unit weights every tail weight is
`1`, so the bit form collapses to `ρ₁(N) = ∑_j b_j(N)`; comparing with
the corpus's `dyadicDefect_one`, which evaluates `ρ₁(N)` as the binary
digit sum through Legendre's count, forces

`∑_j b_j(N) = S₂(N)`.

The statement is an independently meaningful arithmetic identity, and
its proof runs entirely through the new tail weight and the new
exchange of summation.  A wrong index convention in `dyadicTailWeight`,
or a wrong exchange, would move one of the two sides and leave the
derivation unclosable; so this theorem is the machine-checked
regression test for the bit form, in the same role that
`dyadicDefect_one` plays for the defect form. -/
theorem tsum_testBit_eq_digitSum (N : ℕ) :
    ∑' j : ℕ, ((N.testBit j).toNat : ℝ) =
      ((Nat.digits 2 N).sum : ℝ) := by
  calc ∑' j : ℕ, ((N.testBit j).toNat : ℝ)
      = ∑' j : ℕ, ((N.testBit j).toNat : ℝ) *
          dyadicTailWeight (fun _ ↦ (1 : ℝ)) j := by
        refine tsum_congr fun j ↦ ?_
        rw [dyadicTailWeight_one, mul_one]
    _ = dyadicDefect (fun _ ↦ (1 : ℝ)) N :=
        (dyadicDefect_eq_tsum_testBit
          (fun _ ↦ (1 : ℝ)) N summable_abs_one).symm
    _ = ((Nat.digits 2 N).sum : ℝ) := dyadicDefect_one N

end Fabius
