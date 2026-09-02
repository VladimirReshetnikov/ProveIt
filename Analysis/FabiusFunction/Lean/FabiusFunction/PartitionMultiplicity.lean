import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-!
# Partitions as multiplicity vectors

A partition of `n` (Mathlib's `Nat.Partition n`: a multiset of positive integers with sum `n`)
is determined by its multiplicity vector `k ↦ #{parts equal to k+1}`, and, since every part is
at most `n`, the alphabet `{1, …, N}` suffices as soon as `n ≤ N`.  Conversely every
`m : Fin N → ℕ` with `∑_k (k+1) m_k = n` is the multiplicity vector of exactly one partition of
`n`.  This is the bijection behind the product formula `∑_n p(n) q^n = ∏_k (1 - q^k)^{-1}`.

## Main declarations

* `partMultiplicity`, `multisetOfMultiplicity`, `partitionOfMultiplicity`.
* `parts_eq_multisetOfMultiplicity`: a partition is recovered from its multiplicities.
* `partitionEquivMultiplicity`: `Nat.Partition n ≃ {m : Fin N → ℕ // ∑ (k+1) m_k = n}` for
  `n ≤ N`.
* `multiplicityVectors`, `card_partition_eq_card_multiplicityVectors`:
  `p(n) = #{m : Fin N → ℕ | ∑ (k+1) m_k = n}` for `n ≤ N`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The multiplicity vector `k ↦ #{parts equal to k+1}` of a partition, on the alphabet
`{1, …, N}`. -/
def partMultiplicity {n : ℕ} (N : ℕ) (p : Nat.Partition n) : Fin N → ℕ :=
  fun k => p.parts.count ((k : ℕ) + 1)

/-- The multiset with `m k` copies of `k + 1`. -/
def multisetOfMultiplicity {N : ℕ} (m : Fin N → ℕ) : Multiset ℕ :=
  ∑ k : Fin N, Multiset.replicate (m k) ((k : ℕ) + 1)

theorem sum_multisetOfMultiplicity {N : ℕ} (m : Fin N → ℕ) :
    (multisetOfMultiplicity m).sum = ∑ k : Fin N, ((k : ℕ) + 1) * m k := by
  unfold multisetOfMultiplicity
  rw [← Multiset.coe_sumAddMonoidHom, map_sum]
  simp only [Multiset.coe_sumAddMonoidHom, Multiset.sum_replicate, smul_eq_mul]
  exact sum_congr rfl fun k _ => mul_comm _ _

theorem count_multisetOfMultiplicity {N : ℕ} (m : Fin N → ℕ) (k : Fin N) :
    (multisetOfMultiplicity m).count ((k : ℕ) + 1) = m k := by
  unfold multisetOfMultiplicity
  rw [Multiset.count_sum', Finset.sum_eq_single k]
  · simp [Multiset.count_replicate]
  · intro j _ hj
    rw [Multiset.count_replicate, if_neg]
    intro h
    apply hj
    exact Fin.ext (by omega)
  · intro h
    exact absurd (mem_univ k) h

theorem pos_of_mem_multisetOfMultiplicity {N : ℕ} {m : Fin N → ℕ} {i : ℕ}
    (hi : i ∈ multisetOfMultiplicity m) : 0 < i := by
  unfold multisetOfMultiplicity at hi
  rw [Multiset.mem_sum] at hi
  obtain ⟨k, -, hk⟩ := hi
  rw [Multiset.mem_replicate] at hk
  omega

/-- The partition of `n` with multiplicity vector `m` (when `∑ (k+1) m_k = n`). -/
def partitionOfMultiplicity (n : ℕ) {N : ℕ} (m : Fin N → ℕ)
    (h : ∑ k : Fin N, ((k : ℕ) + 1) * m k = n) : Nat.Partition n :=
  Nat.Partition.ofSums n (multisetOfMultiplicity m) (by rw [sum_multisetOfMultiplicity, h])

theorem partitionOfMultiplicity_parts (n : ℕ) {N : ℕ} (m : Fin N → ℕ)
    (h : ∑ k : Fin N, ((k : ℕ) + 1) * m k = n) :
    (partitionOfMultiplicity n m h).parts = multisetOfMultiplicity m := by
  unfold partitionOfMultiplicity
  rw [Nat.Partition.ofSums_parts, Multiset.filter_eq_self]
  intro i hi
  exact (pos_of_mem_multisetOfMultiplicity hi).ne'

/-- A partition of `n ≤ N` is recovered from its multiplicity vector on `{1, …, N}`. -/
theorem parts_eq_multisetOfMultiplicity {n N : ℕ} (hN : n ≤ N) (p : Nat.Partition n) :
    p.parts = multisetOfMultiplicity (partMultiplicity N p) := by
  ext i
  unfold multisetOfMultiplicity partMultiplicity
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rcases i with _ | j
  · rw [Multiset.count_eq_zero.mpr fun h => (p.parts_pos h).ne' rfl]
    symm
    exact sum_eq_zero fun k _ => if_neg (by omega)
  · by_cases hj : j < N
    · rw [sum_eq_single ⟨j, hj⟩]
      · simp
      · intro k _ hk
        rw [if_neg]
        intro h
        apply hk
        exact Fin.ext (show (k : ℕ) = j by omega)
      · intro h
        exact absurd (mem_univ _) h
    · have h0 : p.parts.count (j + 1) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        have := Nat.Partition.le_of_mem_parts hmem
        omega
      rw [h0]
      symm
      exact sum_eq_zero fun k _ => if_neg (by omega)

theorem sum_partMultiplicity {n N : ℕ} (hN : n ≤ N) (p : Nat.Partition n) :
    ∑ k : Fin N, ((k : ℕ) + 1) * partMultiplicity N p k = n := by
  rw [← sum_multisetOfMultiplicity, ← parts_eq_multisetOfMultiplicity hN, p.parts_sum]

/-- **Partitions as multiplicity vectors**: for `n ≤ N`,
`Nat.Partition n ≃ {m : Fin N → ℕ // ∑ (k+1) m_k = n}`. -/
def partitionEquivMultiplicity (n N : ℕ) (hN : n ≤ N) :
    Nat.Partition n ≃ {m : Fin N → ℕ // ∑ k : Fin N, ((k : ℕ) + 1) * m k = n} where
  toFun p := ⟨partMultiplicity N p, sum_partMultiplicity hN p⟩
  invFun m := partitionOfMultiplicity n m.1 m.2
  left_inv p := by
    apply Nat.Partition.ext
    rw [partitionOfMultiplicity_parts, ← parts_eq_multisetOfMultiplicity hN]
  right_inv m := by
    apply Subtype.ext
    funext k
    show (partitionOfMultiplicity n m.1 m.2).parts.count ((k : ℕ) + 1) = m.1 k
    rw [partitionOfMultiplicity_parts, count_multisetOfMultiplicity]

/-- The multiplicity vectors of weight `n` on the alphabet `{1, …, N}`. -/
def multiplicityVectors (N n : ℕ) : Finset (Fin N → ℕ) :=
  (Fintype.piFinset fun _ : Fin N => range (n + 1)).filter
    fun m => ∑ k : Fin N, ((k : ℕ) + 1) * m k = n

theorem mem_multiplicityVectors {N n : ℕ} {m : Fin N → ℕ} :
    m ∈ multiplicityVectors N n ↔ ∑ k : Fin N, ((k : ℕ) + 1) * m k = n := by
  unfold multiplicityVectors
  rw [mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun k => ?_, h⟩
    rw [mem_range]
    have h1 : m k ≤ ((k : ℕ) + 1) * m k := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h2 : ((k : ℕ) + 1) * m k ≤ ∑ j : Fin N, ((j : ℕ) + 1) * m j :=
      single_le_sum (f := fun j : Fin N => ((j : ℕ) + 1) * m j) (fun _ _ => Nat.zero_le _)
        (mem_univ k)
    omega

/-- **The partition count as a count of multiplicity vectors**: for `n ≤ N`,
`p(n) = #{m : Fin N → ℕ | ∑ (k+1) m_k = n}`. -/
theorem card_partition_eq_card_multiplicityVectors {n N : ℕ} (hN : n ≤ N) :
    Fintype.card (Nat.Partition n) = (multiplicityVectors N n).card := by
  rw [← Fintype.card_coe (multiplicityVectors N n)]
  exact Fintype.card_congr ((partitionEquivMultiplicity n N hN).trans
    (Equiv.subtypeEquivRight fun m => mem_multiplicityVectors.symm))

/-- Multiplicity vectors of weight `n` inject into the partitions of `n`, for every alphabet
size `N`: `#{m : Fin N → ℕ | ∑ (k+1) m_k = n} ≤ p(n)`. -/
theorem card_multiplicityVectors_le (N n : ℕ) :
    (multiplicityVectors N n).card ≤ Fintype.card (Nat.Partition n) := by
  rw [← Fintype.card_coe (multiplicityVectors N n)]
  refine Fintype.card_le_of_injective
    (fun m => partitionOfMultiplicity n m.1 (mem_multiplicityVectors.mp m.2)) ?_
  intro m m' h
  apply Subtype.ext
  funext k
  have := congrArg (fun p : Nat.Partition n => p.parts.count ((k : ℕ) + 1)) h
  simpa only [partitionOfMultiplicity_parts, count_multisetOfMultiplicity] using this

end Fabius
