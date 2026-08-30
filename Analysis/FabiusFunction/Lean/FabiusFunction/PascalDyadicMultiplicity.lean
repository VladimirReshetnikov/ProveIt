import FabiusFunction.DyadicZeroMultiplicity
import FabiusFunction.WeightedScaleMultiplicity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Pascal-weighted dyadic multiplicities

The rank-`r` Pascal--Rvachev product in the spectral-arithmetic frontier has
integer-zero multiplicity

`choose (1 + ν₂(n)) r`.

The existing `dyadicZeroMultiplicity n = 1 + ν₂(n)` is precisely the
upper argument of this binomial coefficient.  This module develops the finite
arithmetic of the entire Pascal column, independently of any claim that an
analytic product exists.

There are two deliberate totalization conventions:

* `pascalDyadicMultiplicity r 0 = 0`, because frequency zero is not an
  integer zero of the sinc product;
* rank zero is retained as the constant multiplicity one on positive indices.
  The report starts at rank one, but rank zero makes Pascal recurrence and the
  rank-generating polynomial uniform.

The main results are:

* `pascalDyadicMultiplicity_succ_two_mul`, Pascal's rule under one dyadic
  dilation;
* `pascalDyadicMultiplicity_two_pow_mul`, its all-scales Vandermonde form;
* `pascalDyadicMultiplicity_succ_eq_weightedScaleMultiplicity`, the bridge to
  the base-generic layer-cake calculus;
* `pascalDyadicMultiplicity_succ_eq_sum_scaleWeights`, the hockey-stick
  interpretation as a sum over active dyadic scales;
* `finitePascalDyadicPrefixMultiplicity_succ_eq_scaleCount`, the exact
  finite-product scale formula;
* `card_pascalDyadicMultiplicity_succ_ne_zero`, the exact finite support count;
* `pascalDyadicPrefixMultiplicity_succ_eq_scaleCount`, the exact floor-sum
  formula for every finite prefix;
* `sum_pascalDyadicMultiplicity_mul_pow`, the binomial rank-generating
  polynomial over an arbitrary commutative semiring.

All statements are finite and algebraic.  No Dirichlet-series, Mellin,
canonical-product, or Fourier-analytic consequence is asserted here.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## Definition and elementary ranks -/

/-- The totalized rank-`r` Pascal dyadic multiplicity.

At a positive integer `n` this is
`choose (dyadicZeroMultiplicity n) r = choose (1 + ν₂(n)) r`.  Its value
at `n = 0` is explicitly zero, rather than the accidental value obtained by
feeding Mathlib's totalized `padicValNat` at zero into the binomial formula.
Rank zero is the constant sequence one on positive indices. -/
def pascalDyadicMultiplicity (r n : ℕ) : ℕ :=
  if n = 0 then 0 else (dyadicZeroMultiplicity n).choose r

/-- Frequency zero carries no Pascal dyadic multiplicity. -/
@[simp] theorem pascalDyadicMultiplicity_zero (r : ℕ) :
    pascalDyadicMultiplicity r 0 = 0 := by
  simp [pascalDyadicMultiplicity]

/-- On a positive index, the totalized definition is the report's binomial
formula. -/
theorem pascalDyadicMultiplicity_of_pos (r n : ℕ) (hn : 1 ≤ n) :
    pascalDyadicMultiplicity r n = (dyadicZeroMultiplicity n).choose r := by
  simp [pascalDyadicMultiplicity, Nat.one_le_iff_ne_zero.mp hn]

/-- Successor indices expose the binomial formula without a side condition. -/
@[simp] theorem pascalDyadicMultiplicity_succ (r n : ℕ) :
    pascalDyadicMultiplicity r (n + 1) =
      (dyadicZeroMultiplicity (n + 1)).choose r := by
  exact pascalDyadicMultiplicity_of_pos r (n + 1) (by omega)

/-- Rank zero is one at every positive integer. -/
@[simp] theorem pascalDyadicMultiplicity_zero_rank (n : ℕ) (hn : 1 ≤ n) :
    pascalDyadicMultiplicity 0 n = 1 := by
  rw [pascalDyadicMultiplicity_of_pos 0 n hn, Nat.choose_zero_right]

/-- Rank zero on a successor index is definitionally the constant sequence. -/
@[simp] theorem pascalDyadicMultiplicity_zero_rank_succ (n : ℕ) :
    pascalDyadicMultiplicity 0 (n + 1) = 1 := by
  exact pascalDyadicMultiplicity_zero_rank (n + 1) (by omega)

/-- Rank one recovers the classical multiplicity `1 + ν₂(n)` exactly. -/
theorem pascalDyadicMultiplicity_one (n : ℕ) (hn : 1 ≤ n) :
    pascalDyadicMultiplicity 1 n = dyadicZeroMultiplicity n := by
  rw [pascalDyadicMultiplicity_of_pos 1 n hn, Nat.choose_one_right]

/-- The rank-one recovery specialized to successor indices. -/
@[simp] theorem pascalDyadicMultiplicity_one_succ (n : ℕ) :
    pascalDyadicMultiplicity 1 (n + 1) =
      dyadicZeroMultiplicity (n + 1) := by
  exact pascalDyadicMultiplicity_one (n + 1) (by omega)

/-- The first positive frequency has the first row of Pascal's triangle as
its rank profile. -/
@[simp] theorem pascalDyadicMultiplicity_one_index (r : ℕ) :
    pascalDyadicMultiplicity r 1 = (1 : ℕ).choose r := by
  rw [pascalDyadicMultiplicity_of_pos r 1 (by omega),
    dyadicZeroMultiplicity_one]

/-- At the dyadic level `2^a`, the rank profile is row `a + 1` of Pascal's
triangle. -/
@[simp] theorem pascalDyadicMultiplicity_two_pow (r a : ℕ) :
    pascalDyadicMultiplicity r (2 ^ a) = (a + 1).choose r := by
  rw [pascalDyadicMultiplicity_of_pos r (2 ^ a) Nat.one_le_two_pow,
    dyadicZeroMultiplicity_two_pow]

/-! ## Support and dyadic scale recurrence -/

/-- At a positive integer, rank `r` occurs exactly while `r` is no larger
than the classical dyadic multiplicity. -/
theorem pascalDyadicMultiplicity_ne_zero_iff
    (r n : ℕ) (hn : 1 ≤ n) :
    pascalDyadicMultiplicity r n ≠ 0 ↔ r ≤ dyadicZeroMultiplicity n := by
  rw [pascalDyadicMultiplicity_of_pos r n hn, Nat.choose_ne_zero_iff]

/-- The rank-`r+1` multiplicity is supported precisely on multiples of
`2^r`.  Thus increasing rank thins the integer support without changing its
dyadic nature. -/
theorem pascalDyadicMultiplicity_succ_ne_zero_iff_pow_two_dvd
    (r n : ℕ) (hn : 1 ≤ n) :
    pascalDyadicMultiplicity (r + 1) n ≠ 0 ↔ 2 ^ r ∣ n := by
  rw [pascalDyadicMultiplicity_ne_zero_iff (r + 1) n hn,
    dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd n r hn]

/-- Odd positive indices carry the first row of Pascal's triangle. -/
@[simp] theorem pascalDyadicMultiplicity_two_mul_add_one (r n : ℕ) :
    pascalDyadicMultiplicity r (2 * n + 1) = (1 : ℕ).choose r := by
  rw [pascalDyadicMultiplicity_of_pos r (2 * n + 1) (by omega),
    dyadicZeroMultiplicity_two_mul_add_one]

/-- **Pascal scale recurrence.**  Doubling a positive integer increments the
upper binomial argument, so the rank-`r+1` multiplicity splits into ranks `r`
and `r+1` at the undoubled index. -/
theorem pascalDyadicMultiplicity_succ_two_mul
    (r n : ℕ) (hn : 1 ≤ n) :
    pascalDyadicMultiplicity (r + 1) (2 * n) =
      pascalDyadicMultiplicity r n + pascalDyadicMultiplicity (r + 1) n := by
  rw [pascalDyadicMultiplicity_of_pos (r + 1) (2 * n) (by omega),
    dyadicZeroMultiplicity_two_mul n hn,
    pascalDyadicMultiplicity_of_pos r n hn,
    pascalDyadicMultiplicity_of_pos (r + 1) n hn,
    Nat.choose_succ_succ']

/-- **All-scales Pascal recurrence.**  Extracting `a` factors of two is
Vandermonde convolution between the rank profile at `n` and the `a`-th row of
Pascal's triangle. -/
theorem pascalDyadicMultiplicity_two_pow_mul
    (a r n : ℕ) (hn : 1 ≤ n) :
    pascalDyadicMultiplicity r (2 ^ a * n) =
      ∑ ij ∈ Finset.antidiagonal r,
        pascalDyadicMultiplicity ij.1 n * a.choose ij.2 := by
  rw [pascalDyadicMultiplicity_of_pos r (2 ^ a * n)
      (Nat.mul_pos (Nat.two_pow_pos a) (by omega)),
    dyadicZeroMultiplicity_two_pow_mul a n hn,
    Nat.add_choose_eq]
  apply Finset.sum_congr rfl
  intro ij _hij
  rw [pascalDyadicMultiplicity_of_pos ij.1 n hn]

/-! ## Hockey-stick expansion -/

/-- A zero-based hockey-stick identity: summing a fixed Pascal column through
row `m - 1` gives the next entry in the following row. -/
theorem sum_range_choose_fixed (m r : ℕ) :
    ∑ h ∈ range m, h.choose r = m.choose (r + 1) := by
  cases m with
  | zero => simp
  | succ m =>
      simpa [inclusivePrefixSum] using inclusivePrefixSum_choose m r

/-- The positive rank-`r+1` dyadic multiplicity is exactly the Pascal-weight
specialization of the base-generic scale-multiplicity calculus.

This bridge lets cumulative dyadic counts reuse the finite layer-cake theorem
from `WeightedScaleMultiplicity`, rather than repeating its Fubini argument. -/
theorem pascalDyadicMultiplicity_succ_eq_weightedScaleMultiplicity
    (r n : ℕ) (hn : 1 ≤ n) :
    pascalDyadicMultiplicity (r + 1) n =
      weightedScaleMultiplicity 2 (fun h ↦ h.choose r) n := by
  rw [pascalDyadicMultiplicity_of_pos (r + 1) n hn,
    weightedScaleMultiplicity_choose, dyadicZeroMultiplicity]

/-- The rank-`r+1` multiplicity is the sum of the Pascal scale weights
`choose h r` over exactly the active dyadic scales.  This is the finite
hockey-stick identity behind the report's zero-multiplicity formula. -/
theorem pascalDyadicMultiplicity_succ_eq_sum_scaleWeights
    (r n : ℕ) (hn : 1 ≤ n) :
    pascalDyadicMultiplicity (r + 1) n =
      ∑ h ∈ range (dyadicZeroMultiplicity n), h.choose r := by
  rw [pascalDyadicMultiplicity_succ_eq_weightedScaleMultiplicity r n hn,
    weightedScaleMultiplicity, inclusivePrefixSum, dyadicZeroMultiplicity]

/-! ## Finite-scale truncation -/

/-- The rank-`r`, `M`-scale Pascal dyadic multiplicity.

At a positive integer this is
`choose (min M (1 + ν₂(n))) r`, exactly the finite-product multiplicity in
the report.  As for `pascalDyadicMultiplicity`, its value at index zero is
explicitly set to zero. -/
def finitePascalDyadicMultiplicity (r M n : ℕ) : ℕ :=
  if n = 0 then 0 else (min M (dyadicZeroMultiplicity n)).choose r

/-- Index zero carries no finite-scale Pascal multiplicity. -/
@[simp] theorem finitePascalDyadicMultiplicity_zero (r M : ℕ) :
    finitePascalDyadicMultiplicity r M 0 = 0 := by
  simp [finitePascalDyadicMultiplicity]

/-- The finite-scale multiplicity formula on a positive index. -/
theorem finitePascalDyadicMultiplicity_of_pos
    (r M n : ℕ) (hn : 1 ≤ n) :
    finitePascalDyadicMultiplicity r M n =
      (min M (dyadicZeroMultiplicity n)).choose r := by
  simp [finitePascalDyadicMultiplicity, Nat.one_le_iff_ne_zero.mp hn]

/-- Rank zero remains one on positive indices after every scale truncation. -/
@[simp] theorem finitePascalDyadicMultiplicity_zero_rank_succ
    (M n : ℕ) :
    finitePascalDyadicMultiplicity 0 M (n + 1) = 1 := by
  rw [finitePascalDyadicMultiplicity_of_pos 0 M (n + 1) (by omega),
    Nat.choose_zero_right]

/-- With zero retained scales, every positive analytic rank has zero
multiplicity. -/
@[simp] theorem finitePascalDyadicMultiplicity_succ_zero_scale
    (r n : ℕ) :
    finitePascalDyadicMultiplicity (r + 1) 0 (n + 1) = 0 := by
  rw [finitePascalDyadicMultiplicity_of_pos
    (r + 1) 0 (n + 1) (by omega)]
  simp

/-- At the dyadic level `2^a`, truncation at `M` scales gives row
`min M (a + 1)` of Pascal's triangle. -/
@[simp] theorem finitePascalDyadicMultiplicity_two_pow
    (r M a : ℕ) :
    finitePascalDyadicMultiplicity r M (2 ^ a) =
      (min M (a + 1)).choose r := by
  rw [finitePascalDyadicMultiplicity_of_pos r M (2 ^ a) Nat.one_le_two_pow,
    dyadicZeroMultiplicity_two_pow]

/-- Once the cutoff contains every active dyadic scale, the finite and full
multiplicities agree. -/
theorem finitePascalDyadicMultiplicity_eq_full_of_le
    (r M n : ℕ) (hn : 1 ≤ n) (hactive : dyadicZeroMultiplicity n ≤ M) :
    finitePascalDyadicMultiplicity r M n =
      pascalDyadicMultiplicity r n := by
  rw [finitePascalDyadicMultiplicity_of_pos r M n hn,
    pascalDyadicMultiplicity_of_pos r n hn, min_eq_right hactive]

/-- Finite-scale hockey-stick expansion: only the first
`min M (1 + ν₂(n))` Pascal weights are active. -/
theorem finitePascalDyadicMultiplicity_succ_eq_sum_scaleWeights
    (r M n : ℕ) (hn : 1 ≤ n) :
    finitePascalDyadicMultiplicity (r + 1) M n =
      ∑ h ∈ range (min M (dyadicZeroMultiplicity n)), h.choose r := by
  rw [finitePascalDyadicMultiplicity_of_pos (r + 1) M n hn,
    sum_range_choose_fixed]

/-- The finite rank-`r+1` multiplicity is nonzero precisely when the cutoff
has reached rank `r+1` and the index is divisible by `2^r`. -/
theorem finitePascalDyadicMultiplicity_succ_ne_zero_iff
    (r M n : ℕ) (hn : 1 ≤ n) :
    finitePascalDyadicMultiplicity (r + 1) M n ≠ 0 ↔
      r + 1 ≤ M ∧ 2 ^ r ∣ n := by
  rw [finitePascalDyadicMultiplicity_of_pos (r + 1) M n hn,
    Nat.choose_ne_zero_iff, le_min_iff,
    dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd n r hn]

/-! ## Exact support and dyadic-level distribution -/

/-- Among `1, …, N`, exactly `⌊N / 2^r⌋` indices carry a nonzero
rank-`r+1` Pascal multiplicity. -/
theorem card_pascalDyadicMultiplicity_succ_ne_zero (N r : ℕ) :
    ((range N).filter
      (fun k => pascalDyadicMultiplicity (r + 1) (k + 1) ≠ 0)).card =
        N / 2 ^ r := by
  have hfilter :
      (range N).filter
          (fun k => pascalDyadicMultiplicity (r + 1) (k + 1) ≠ 0) =
        (range N).filter
          (fun k => r + 1 ≤ dyadicZeroMultiplicity (k + 1)) := by
    ext k
    simp only [mem_filter, mem_range]
    exact and_congr_right fun _hk =>
      pascalDyadicMultiplicity_ne_zero_iff (r + 1) (k + 1) (by omega)
  rw [hfilter, card_dyadicZeroMultiplicity_ge_succ]

/-- **Exact dyadic-level contribution.**  The integers through `N` whose
classical dyadic multiplicity is exactly `h + 1` contribute

`(⌊N / 2^h⌋ - ⌊N / 2^(h+1)⌋) * choose (h+1) r`

to the rank-`r` prefix count.  Stating the theorem as a weighted sum avoids
the false suggestion that different dyadic levels always give different
binomial multiplicities (they do not, for example, below rank `r`). -/
theorem sum_pascalDyadicMultiplicity_at_dyadicLevel
    (N r h : ℕ) :
    ∑ k ∈ (range N).filter
        (fun k => dyadicZeroMultiplicity (k + 1) = h + 1),
        pascalDyadicMultiplicity r (k + 1) =
      (N / 2 ^ h - N / 2 ^ (h + 1)) * (h + 1).choose r := by
  calc
    (∑ k ∈ (range N).filter
        (fun k => dyadicZeroMultiplicity (k + 1) = h + 1),
        pascalDyadicMultiplicity r (k + 1)) =
      ∑ _k ∈ (range N).filter
        (fun k => dyadicZeroMultiplicity (k + 1) = h + 1),
        (h + 1).choose r := by
      apply Finset.sum_congr rfl
      intro k hk
      have hlevel : dyadicZeroMultiplicity (k + 1) = h + 1 :=
        (mem_filter.mp hk).2
      rw [pascalDyadicMultiplicity_succ, hlevel]
    _ = ((range N).filter
        (fun k => dyadicZeroMultiplicity (k + 1) = h + 1)).card *
          (h + 1).choose r := by
      simp
    _ = (N / 2 ^ h - N / 2 ^ (h + 1)) * (h + 1).choose r := by
      rw [card_dyadicZeroMultiplicity_eq_succ]

/-! ## Exact finite spectral counts -/

/-- The cumulative rank-`r` Pascal multiplicity on the positive integers
through `N`.  This is the finite arithmetic object denoted `ℕ_r(N)` in the
spectral-arithmetic report. -/
def pascalDyadicPrefixMultiplicity (r N : ℕ) : ℕ :=
  ∑ k ∈ range N, pascalDyadicMultiplicity r (k + 1)

/-- The rank-zero prefix count is the number of positive indices. -/
@[simp] theorem pascalDyadicPrefixMultiplicity_zero_rank (N : ℕ) :
    pascalDyadicPrefixMultiplicity 0 N = N := by
  simp [pascalDyadicPrefixMultiplicity]

/-- Rank one recovers the exact classical count `2N - binaryWeight N`. -/
theorem pascalDyadicPrefixMultiplicity_one (N : ℕ) :
    pascalDyadicPrefixMultiplicity 1 N =
      2 * N - binaryWeight N := by
  rw [pascalDyadicPrefixMultiplicity]
  simpa only [pascalDyadicMultiplicity_one_succ] using
    sum_dyadicZeroMultiplicity_eq N

/-- A positive dyadic multiplicity never exceeds its index.  This elementary
bound is used only to choose a common finite scale range when interchanging
the two sums in `pascalDyadicPrefixMultiplicity_succ_eq_scaleCount`. -/
theorem dyadicZeroMultiplicity_le_self (n : ℕ) (hn : 1 ≤ n) :
    dyadicZeroMultiplicity n ≤ n := by
  rw [dyadicZeroMultiplicity]
  have hval : padicValNat 2 n < n :=
    Nat.padicValNat_lt_self (Nat.one_le_iff_ne_zero.mp hn)
  omega

/-- The cumulative finite-scale rank-`r` multiplicity through `N`. -/
def finitePascalDyadicPrefixMultiplicity (r M N : ℕ) : ℕ :=
  ∑ k ∈ range N, finitePascalDyadicMultiplicity r M (k + 1)

/-- The finite-scale rank-zero prefix is the number of positive indices. -/
@[simp] theorem finitePascalDyadicPrefixMultiplicity_zero_rank (M N : ℕ) :
    finitePascalDyadicPrefixMultiplicity 0 M N = N := by
  simp [finitePascalDyadicPrefixMultiplicity]

/-- For a positive index, the finite hockey-stick sum may be extended to the
common cutoff range `h < M`; outside the active dyadic scales the divisibility
indicator is zero. -/
private theorem finitePascalDyadicMultiplicity_succ_eq_boundedScaleSum
    (M r k : ℕ) :
    finitePascalDyadicMultiplicity (r + 1) M (k + 1) =
      ∑ h ∈ range M,
        if 2 ^ h ∣ k + 1 then h.choose r else 0 := by
  have hpositive : 1 ≤ k + 1 := by omega
  rw [finitePascalDyadicMultiplicity_succ_eq_sum_scaleWeights
    r M (k + 1) hpositive]
  have hrange :
      (range M).filter (fun h => h < dyadicZeroMultiplicity (k + 1)) =
        range (min M (dyadicZeroMultiplicity (k + 1))) := by
    ext h
    simp only [mem_filter, mem_range, lt_min_iff]
  rw [← hrange, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _hh
  have hdiv :
      h < dyadicZeroMultiplicity (k + 1) ↔ 2 ^ h ∣ k + 1 := by
    simpa only [Nat.lt_iff_add_one_le] using
      (dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd
        (k + 1) h hpositive)
  simpa only [hdiv]

/-- **Exact finite-product scale count.**  Summing the truncated
multiplicities through `N` counts each scale by its number of positive
multiples:

`sum_{h < M} choose h r * floor(N / 2^h)`.

This is the finite arithmetic counterpart of the report's truncated sinc
product, with no analytic product needed in its proof. -/
theorem finitePascalDyadicPrefixMultiplicity_succ_eq_scaleCount
    (M N r : ℕ) :
    finitePascalDyadicPrefixMultiplicity (r + 1) M N =
      ∑ h ∈ range M, h.choose r * (N / 2 ^ h) := by
  rw [finitePascalDyadicPrefixMultiplicity]
  calc
    (∑ k ∈ range N, finitePascalDyadicMultiplicity (r + 1) M (k + 1)) =
        ∑ k ∈ range N, ∑ h ∈ range M,
          if 2 ^ h ∣ k + 1 then h.choose r else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact finitePascalDyadicMultiplicity_succ_eq_boundedScaleSum M r k
    _ = ∑ h ∈ range M, ∑ k ∈ range N,
          if 2 ^ h ∣ k + 1 then h.choose r else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ h ∈ range M, h.choose r * (N / 2 ^ h) := by
      apply Finset.sum_congr rfl
      intro h _hh
      rw [← Finset.sum_filter]
      simp [Nat.card_multiples, Nat.mul_comm]

/-- If the scale cutoff `M` is at least the prefix endpoint `N`, then every
active scale at every index in the prefix has been retained. -/
theorem finitePascalDyadicPrefixMultiplicity_eq_full_of_le
    (r M N : ℕ) (hNM : N ≤ M) :
    finitePascalDyadicPrefixMultiplicity r M N =
      pascalDyadicPrefixMultiplicity r N := by
  rw [finitePascalDyadicPrefixMultiplicity,
    pascalDyadicPrefixMultiplicity]
  apply Finset.sum_congr rfl
  intro k hk
  apply finitePascalDyadicMultiplicity_eq_full_of_le r M (k + 1) (by omega)
  exact (dyadicZeroMultiplicity_le_self (k + 1) (by omega)).trans
    ((Nat.succ_le_iff.mpr (mem_range.mp hk)).trans hNM)

/-- **Exact finite scale count.**  The cumulative rank-`r+1` multiplicity is
the finite floor sum

`sum_{h < N} choose h r * floor(N / 2^h)`.

The nominal upper bound `N` is harmless and makes the theorem valid at
`N = 0`; every scale which can divide a positive integer at most `N` is
included.  This is the precise finite arithmetic bridge from Pascal scale
weights to the spectral zero count. -/
theorem pascalDyadicPrefixMultiplicity_succ_eq_scaleCount (N r : ℕ) :
    pascalDyadicPrefixMultiplicity (r + 1) N =
      ∑ h ∈ range N, h.choose r * (N / 2 ^ h) := by
  calc
    pascalDyadicPrefixMultiplicity (r + 1) N =
        ∑ k ∈ range N,
          weightedScaleMultiplicity 2 (fun h ↦ h.choose r) (k + 1) := by
      rw [pascalDyadicPrefixMultiplicity]
      apply Finset.sum_congr rfl
      intro k hk
      exact pascalDyadicMultiplicity_succ_eq_weightedScaleMultiplicity
        r (k + 1) (by omega)
    _ = ∑ h ∈ range N, (N / 2 ^ h) • h.choose r :=
      sum_range_weightedScaleMultiplicity 2 N (fun h ↦ h.choose r) (by omega)
    _ = ∑ h ∈ range N, h.choose r * (N / 2 ^ h) := by
      apply Finset.sum_congr rfl
      intro h _hh
      simp only [Nat.nsmul_eq_mul, Nat.mul_comm]

/-- The exact scale-count formula specialized to a dyadic endpoint, before
discarding the identically zero scales above `M`. -/
theorem pascalDyadicPrefixMultiplicity_succ_two_pow_untruncated (M r : ℕ) :
    pascalDyadicPrefixMultiplicity (r + 1) (2 ^ M) =
      ∑ h ∈ range (2 ^ M), h.choose r * (2 ^ M / 2 ^ h) := by
  exact pascalDyadicPrefixMultiplicity_succ_eq_scaleCount (2 ^ M) r

/-- **Compact dyadic-endpoint count.**  At `N = 2^M`, only scales
`0, …, M` contribute and their multiplicities are exact powers of two:

`ℕ_(r+1)(2^M) = sum_{h=0}^M choose h r * 2^(M-h)`.

This is the finite Pascal shell formula with neither an infinite tail nor a
natural-number division left in the statement. -/
theorem pascalDyadicPrefixMultiplicity_succ_two_pow (M r : ℕ) :
    pascalDyadicPrefixMultiplicity (r + 1) (2 ^ M) =
      ∑ h ∈ range (M + 1), h.choose r * 2 ^ (M - h) := by
  calc
    pascalDyadicPrefixMultiplicity (r + 1) (2 ^ M) =
        ∑ h ∈ range (2 ^ M), h.choose r * (2 ^ M / 2 ^ h) :=
      pascalDyadicPrefixMultiplicity_succ_two_pow_untruncated M r
    _ = ∑ h ∈ range (M + 1), h.choose r * (2 ^ M / 2 ^ h) := by
      refine (Finset.sum_subset (range_mono ?_) ?_).symm
      · exact Nat.succ_le_iff.mpr M.lt_two_pow_self
      · intro h _hlarge hnot
        have hMlt : M < h := by
          simpa only [mem_range, Nat.not_lt, Nat.add_one_le_iff] using hnot
        have hpow : 2 ^ M < 2 ^ h :=
          Nat.pow_lt_pow_right (by omega) hMlt
        rw [Nat.div_eq_of_lt hpow, Nat.mul_zero]
    _ = ∑ h ∈ range (M + 1), h.choose r * 2 ^ (M - h) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Nat.pow_div (Nat.le_of_lt_succ (mem_range.mp hh)) (by omega)]

/-! ## Rank-generating polynomial -/

/-- **Rank-generating polynomial at one positive index.**  Over every
commutative semiring, the complete finite rank profile is the binomial
polynomial

`sum_r μ_r(n) u^r = (1 + u)^(1 + ν₂(n))`.

Keeping rank zero makes this identity division-free; removing its constant
term recovers the report's positive-rank generating function. -/
theorem sum_pascalDyadicMultiplicity_mul_pow
    {R : Type*} [CommSemiring R] (n : ℕ) (hn : 1 ≤ n) (u : R) :
    ∑ r ∈ range (dyadicZeroMultiplicity n + 1),
        (pascalDyadicMultiplicity r n : R) * u ^ r =
      (1 + u) ^ dyadicZeroMultiplicity n := by
  have hcoefficient (r : ℕ) :
      pascalDyadicMultiplicity r n =
        (dyadicZeroMultiplicity n).choose r :=
    pascalDyadicMultiplicity_of_pos r n hn
  simp_rw [hcoefficient]
  simpa only [one_pow, mul_one, mul_comm, add_comm] using
    (add_pow u 1 (dyadicZeroMultiplicity n)).symm

end Fabius
