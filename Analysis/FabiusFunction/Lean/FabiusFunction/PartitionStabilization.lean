import FabiusFunction.PartitionMultiplicity
import FabiusFunction.PartitionGeneratingFunction
import FabiusFunction.BoxPartitions
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Stabilization of the Gaussian coefficients

For `m, k ≥ N` the coefficient of `q^N` in `[m+k, k]_q` is `p(N)`: the Gaussian coefficient
enumerates the partitions in a `k × m` box by size (`BoxPartitions`), and every partition of `N`
fits in the box as soon as `m, k ≥ N`.

The bijection between the partitions of `N` and the box partitions of size `N` is
*conjugation*, read through multiplicity vectors: a multiplicity vector `μ : Fin N → ℕ` of
weight `N` is sent to the antitone sequence `j ↦ ∑_{i ≥ j} μ_i` (the number of parts exceeding
`j`, i.e. the `j`-th part of the conjugate partition), padded with zeros to length `k`; the
inverse takes consecutive differences.

## Main declarations

* `conjugateVector`, `differenceVector`, `differenceVector_conjugateVector`,
  `conjugateVector_differenceVector`.
* `card_boxPartitions_filter_sum`: `#{λ ∈ box(k,m) | |λ| = N} = p(N)` for `m, k ≥ N`.
* `coeff_gaussianBinomial_X_eq_partitionCount`: the stabilization of the coefficients.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-- Extension of a vector on `Fin k` by zero. -/
def extZero {k : ℕ} (l : Fin k → ℕ) (t : ℕ) : ℕ := if h : t < k then l ⟨t, h⟩ else 0

/-- Inside the range, `extZero l` is just `l`: `extZero l t = l ⟨t, h⟩` for `t < k`. -/
theorem extZero_of_lt {k : ℕ} (l : Fin k → ℕ) {t : ℕ} (h : t < k) : extZero l t = l ⟨t, h⟩ := by
  unfold extZero
  rw [dif_pos h]

/-- Past the range, `extZero l` vanishes: `extZero l t = 0` for `k ≤ t`. This is the padding by
zeros that lets a partition with at most `k` parts be read as a sequence indexed by all of `ℕ`. -/
theorem extZero_of_le {k : ℕ} (l : Fin k → ℕ) {t : ℕ} (h : k ≤ t) : extZero l t = 0 := by
  unfold extZero
  rw [dif_neg (not_lt.mpr h)]

/-- Zero-padding preserves antitonicity: if `l` is antitone on `Fin k` then `extZero l` is
antitone on all of `ℕ`. Crossing the boundary `k` is harmless because the padded values are `0`,
which is below every value of `l`. -/
theorem extZero_antitone {k : ℕ} {l : Fin k → ℕ} (hl : ∀ i j : Fin k, i ≤ j → l j ≤ l i)
    {s t : ℕ} (hst : s ≤ t) : extZero l t ≤ extZero l s := by
  by_cases ht : t < k
  · rw [extZero_of_lt l ht, extZero_of_lt l (lt_of_le_of_lt hst ht)]
    exact hl _ _ (Fin.mk_le_mk.mpr hst)
  · rw [extZero_of_le l (not_lt.mp ht)]
    exact Nat.zero_le _

/-- The conjugate of a multiplicity vector: `j ↦ ∑_{i ≥ j} μ_i`, on `Fin k`. -/
def conjugateVector {N : ℕ} (k : ℕ) (μ : Fin N → ℕ) : Fin k → ℕ :=
  fun j => ∑ i : Fin N, if (j : ℕ) ≤ i then μ i else 0

/-- The consecutive differences of a sequence on `Fin k`, read on `Fin N`. -/
def differenceVector (N : ℕ) {k : ℕ} (l : Fin k → ℕ) : Fin N → ℕ :=
  fun i => extZero l i - extZero l (i + 1)

/-- The tail sum `∑_{i ≥ t} μ_i` as a function of `t : ℕ`. -/
def tailSumAt {N : ℕ} (μ : Fin N → ℕ) (t : ℕ) : ℕ := ∑ i : Fin N, if t ≤ i then μ i else 0

/-- The zero-padded conjugate is the tail sum, at every `t : ℕ`, once `k ≥ N`: on `t < k` this is
`conjugateVector` by definition, and for `t ≥ k ≥ N` both sides are `0` because no index of
`Fin N` reaches `t`. -/
theorem extZero_conjugateVector {N k : ℕ} (hk : N ≤ k) (μ : Fin N → ℕ) (t : ℕ) :
    extZero (conjugateVector k μ) t = tailSumAt μ t := by
  by_cases ht : t < k
  · rw [extZero_of_lt _ ht]
    rfl
  · rw [extZero_of_le _ (not_lt.mp ht)]
    unfold tailSumAt
    symm
    exact sum_eq_zero fun i _ => if_neg (by omega)

/-- Peeling the first term off a tail sum: `∑_{i ≥ t} μ_i = μ_t + ∑_{i ≥ t+1} μ_i` for `t < N`.
This is the recursion that makes `differenceVector` invert `conjugateVector`. -/
theorem tailSumAt_succ {N : ℕ} (μ : Fin N → ℕ) {t : ℕ} (ht : t < N) :
    tailSumAt μ t = μ ⟨t, ht⟩ + tailSumAt μ (t + 1) := by
  unfold tailSumAt
  rw [← sum_filter, ← sum_filter, ← add_sum_erase _ _
    (show (⟨t, ht⟩ : Fin N) ∈ univ.filter (fun i : Fin N => t ≤ (i : ℕ)) by simp)]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_erase, mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    omega
  · intro h
    exact ⟨by omega, by omega⟩

/-- A tail sum starting beyond the last index is empty: `∑_{i ≥ t} μ_i = 0` for `t ≥ N`. -/
theorem tailSumAt_of_le {N : ℕ} (μ : Fin N → ℕ) {t : ℕ} (ht : N ≤ t) : tailSumAt μ t = 0 :=
  sum_eq_zero fun i _ => if_neg (by omega)

/-- The conjugate of a multiplicity vector is a partition, i.e. antitone: `j ≤ j'` implies
`(conjugate μ)_{j'} ≤ (conjugate μ)_j`, since the tail sum `∑_{i ≥ j} μ_i` only loses terms as `j`
grows. This is one half of membership in `boxPartitions k m`. -/
theorem conjugateVector_antitone {N k : ℕ} (μ : Fin N → ℕ) :
    ∀ j j' : Fin k, j ≤ j' → conjugateVector k μ j' ≤ conjugateVector k μ j := by
  intro j j' hjj'
  unfold conjugateVector
  refine sum_le_sum fun i _ => ?_
  by_cases h : (j' : ℕ) ≤ i
  · rw [if_pos h, if_pos (le_trans (Fin.le_def.mp hjj') h)]
  · rw [if_neg h]
    exact Nat.zero_le _

/-- Every part of the conjugate is bounded by the weight `∑_i (i+1) μ_i` of `μ`: each surviving
term `μ_i` in `∑_{i ≥ j} μ_i` is at most `(i+1) μ_i`. With weight `N ≤ m` this is the other half
of membership in `boxPartitions k m` — the conjugate fits in a box of width `m`. -/
theorem conjugateVector_le_weight {N k : ℕ} (μ : Fin N → ℕ) (j : Fin k) :
    conjugateVector k μ j ≤ ∑ i : Fin N, ((i : ℕ) + 1) * μ i := by
  unfold conjugateVector
  refine sum_le_sum fun i _ => ?_
  split_ifs
  · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  · exact Nat.zero_le _

/-- `∑_j (conjugate μ)_j = ∑_i (i+1) μ_i` when `k ≥ N`. -/
theorem sum_conjugateVector {N k : ℕ} (hk : N ≤ k) (μ : Fin N → ℕ) :
    ∑ j : Fin k, conjugateVector k μ j = ∑ i : Fin N, ((i : ℕ) + 1) * μ i := by
  unfold conjugateVector
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul]
  congr 1
  have : (univ.filter fun j : Fin k => (j : ℕ) ≤ i) = Iic (⟨i, by omega⟩ : Fin k) := by
    ext j
    simp [Fin.le_def]
  rw [this, Fin.card_Iic]

/-- The differences of the conjugate recover the multiplicities (`k ≥ N`). -/
theorem differenceVector_conjugateVector {N k : ℕ} (hk : N ≤ k) (μ : Fin N → ℕ) :
    differenceVector N (conjugateVector k μ) = μ := by
  funext i
  unfold differenceVector
  rw [extZero_conjugateVector hk, extZero_conjugateVector hk, tailSumAt_succ μ i.isLt,
    Nat.add_sub_cancel]

/-- Telescoping of consecutive differences of an antitone sequence. -/
theorem sum_Ico_sub_succ {e : ℕ → ℕ} (he : ∀ s t, s ≤ t → e t ≤ e s) {a : ℕ} :
    ∀ b, a ≤ b → ∑ t ∈ Ico a b, (e t - e (t + 1)) = e a - e b := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab, ih]
    have h1 := he a b hab
    have h2 := he b (b + 1) (Nat.le_succ b)
    omega

/-- The tail sums of the consecutive differences telescope: for antitone `l`,
`∑_{i ≥ t} (differenceVector N l)_i = extZero l t - extZero l N`, the sum running over `Ico t N`
(and being empty, with both sides `0`, when `t > N`). This is the computation behind
`conjugateVector_differenceVector`. -/
theorem tailSumAt_differenceVector {N k : ℕ} {l : Fin k → ℕ}
    (hl : ∀ i j : Fin k, i ≤ j → l j ≤ l i) (t : ℕ) :
    tailSumAt (differenceVector N l) t = extZero l t - extZero l N := by
  unfold tailSumAt differenceVector
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if t ≤ i then extZero l i - extZero l (i + 1) else 0) N, ← sum_filter]
  have hfilter : (range N).filter (fun i => t ≤ i) = Ico t N := by
    ext i
    simp [mem_Ico, and_comm]
  rw [hfilter]
  rcases le_or_gt t N with htN | htN
  · exact sum_Ico_sub_succ (fun s t hst => extZero_antitone hl hst) N htN
  · rw [Finset.Ico_eq_empty_of_le htN.le, sum_empty]
    symm
    exact Nat.sub_eq_zero_of_le (extZero_antitone hl htN.le)

/-- The conjugate of the differences recovers an antitone sequence vanishing from `N` on. -/
theorem conjugateVector_differenceVector {N k : ℕ} {l : Fin k → ℕ}
    (hl : ∀ i j : Fin k, i ≤ j → l j ≤ l i) (hN : extZero l N = 0) :
    conjugateVector k (differenceVector N l) = l := by
  funext j
  have h := tailSumAt_differenceVector (N := N) hl j
  rw [hN, Nat.sub_zero, extZero_of_lt l j.isLt] at h
  exact h

/-- An antitone sequence with sum `N` vanishes from index `N` on. -/
theorem extZero_eq_zero_of_sum {N k : ℕ} {l : Fin k → ℕ}
    (hl : ∀ i j : Fin k, i ≤ j → l j ≤ l i) (hsum : ∑ j, l j = N) : extZero l N = 0 := by
  by_cases hN : N < k
  · rw [extZero_of_lt l hN]
    by_contra hne
    have hpos : 1 ≤ l ⟨N, hN⟩ := Nat.one_le_iff_ne_zero.mpr hne
    have : N + 1 ≤ ∑ j, l j := by
      calc N + 1 = (Iic (⟨N, hN⟩ : Fin k)).card := by rw [Fin.card_Iic]
        _ = ∑ j ∈ Iic (⟨N, hN⟩ : Fin k), 1 := by rw [sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ j ∈ Iic (⟨N, hN⟩ : Fin k), l j :=
            sum_le_sum fun j hj => le_trans hpos (hl j _ (mem_Iic.mp hj))
        _ ≤ ∑ j, l j := sum_le_sum_of_subset (subset_univ _)
    omega
  · exact extZero_of_le l (not_lt.mp hN)

/-- **Partitions of `N` in a `k × m` box with `m, k ≥ N`**:
`#{λ ∈ box(k,m) : |λ| = N} = p(N)`, by conjugation of multiplicity vectors. -/
theorem card_boxPartitions_filter_sum {N k m : ℕ} (hk : N ≤ k) (hm : N ≤ m) :
    ((boxPartitions k m).filter fun l => ∑ j, l j = N).card = partitionCount N := by
  rw [partitionCount, card_partition_eq_card_multiplicityVectors (le_refl N)]
  symm
  refine Finset.card_bij (fun μ _ => conjugateVector k μ) ?_ ?_ ?_
  · intro μ hμ
    rw [mem_multiplicityVectors] at hμ
    rw [mem_filter, mem_boxPartitions]
    refine ⟨⟨fun j => ?_, conjugateVector_antitone μ⟩, by rw [sum_conjugateVector hk, hμ]⟩
    exact (conjugateVector_le_weight μ j).trans (by rw [hμ]; exact hm)
  · intro μ _ μ' _ h
    have := congrArg (differenceVector N) h
    rwa [differenceVector_conjugateVector hk, differenceVector_conjugateVector hk] at this
  · intro l hl
    rw [mem_filter, mem_boxPartitions] at hl
    obtain ⟨⟨_, hanti⟩, hsum⟩ := hl
    have hN := extZero_eq_zero_of_sum hanti hsum
    refine ⟨differenceVector N l, ?_, conjugateVector_differenceVector hanti hN⟩
    rw [mem_multiplicityVectors, ← sum_conjugateVector hk, conjugateVector_differenceVector hanti hN,
      hsum]

/-- **Stabilization of the Gaussian coefficients**: for `m, k ≥ N` the coefficient of `X^N` in
`[m+k, k]_X` is `p(N)`. -/
theorem coeff_gaussianBinomial_X_eq_partitionCount {R : Type*} [CommRing R] {N k m : ℕ}
    (hk : N ≤ k) (hm : N ≤ m) :
    (gaussianBinomial (X : R[X]) (m + k) k).coeff N = (partitionCount N : R) := by
  rw [← sum_pow_boxSize_eq_gaussianBinomial, finsetSum_coeff]
  simp_rw [coeff_X_pow]
  rw [sum_boole, ← card_boxPartitions_filter_sum hk hm]
  congr 2
  exact filter_congr fun l _ => eq_comm

end Fabius
