import FabiusFunction.PartitionGeneratingFunction

/-!
# Partitions with bounded parts

For `r ≥ 0`, the partitions of `n` with every part at most `r` are exactly the multiplicity
vectors on the alphabet `{1, …, r}` of weight `n`, so their generating function is the finite
product

`∑_n p_{≤ r}(n) q^n = 1/(q;q)_r`   (`‖q‖ < 1`).

## Main declarations

* `parts_eq_multisetOfMultiplicity_of_le`, `card_restricted_le_eq`.
* `boundedCount`, `hasSum_boundedCount_mul_pow`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- A partition whose parts are at most `N` is recovered from its multiplicity vector on
`{1, …, N}`. -/
theorem parts_eq_multisetOfMultiplicity_of_le {n N : ℕ} (p : Nat.Partition n)
    (hp : ∀ i ∈ p.parts, i ≤ N) :
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
        have := hp _ hmem
        omega
      rw [h0]
      symm
      exact sum_eq_zero fun k _ => if_neg (by omega)

/-- `p_{≤ r}(n) = #{m : Fin r → ℕ | ∑ (k+1) m_k = n}` for every `n`. -/
theorem card_restricted_le_eq (r n : ℕ) :
    (Nat.Partition.restricted n (· ≤ r)).card = (multiplicityVectors r n).card := by
  refine Finset.card_bij (fun p _ => partMultiplicity r p) ?_ ?_ ?_
  · intro p hp
    rw [Nat.Partition.restricted, mem_filter] at hp
    rw [mem_multiplicityVectors, ← sum_multisetOfMultiplicity,
      ← parts_eq_multisetOfMultiplicity_of_le p hp.2, p.parts_sum]
  · intro p hp p' hp' h
    rw [Nat.Partition.restricted, mem_filter] at hp hp'
    apply Nat.Partition.ext
    rw [parts_eq_multisetOfMultiplicity_of_le p hp.2, parts_eq_multisetOfMultiplicity_of_le p' hp'.2,
      h]
  · intro m hm
    rw [mem_multiplicityVectors] at hm
    refine ⟨partitionOfMultiplicity n m hm, ?_, ?_⟩
    · rw [Nat.Partition.restricted, mem_filter]
      refine ⟨mem_univ _, fun i hi => ?_⟩
      rw [partitionOfMultiplicity_parts] at hi
      unfold multisetOfMultiplicity at hi
      rw [Multiset.mem_sum] at hi
      obtain ⟨k, -, hk⟩ := hi
      rw [Multiset.mem_replicate] at hk
      omega
    · funext k
      show (partitionOfMultiplicity n m hm).parts.count ((k : ℕ) + 1) = m k
      rw [partitionOfMultiplicity_parts, count_multisetOfMultiplicity]

/-- `p_{≤ r}(n)`: the number of partitions of `n` with every part at most `r`. -/
def boundedCount (r n : ℕ) : ℕ := (Nat.Partition.restricted n (· ≤ r)).card

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Partitions with parts at most `r`**: `∑_n p_{≤ r}(n) q^n = 1/(q;q)_r` for `‖q‖ < 1`. -/
theorem hasSum_boundedCount_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) (r : ℕ) :
    HasSum (fun n : ℕ => (boundedCount r n : 𝕜) * q ^ n) (finiteQPochhammerIn q q r)⁻¹ := by
  have h := hasSum_card_multiplicityVectors hq r
  rw [prod_one_sub_pow_succ_inv] at h
  refine h.congr_fun fun n => ?_
  rw [boundedCount, card_restricted_le_eq]

end Fabius
