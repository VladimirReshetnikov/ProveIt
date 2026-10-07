import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I]

theorem disjoint_powerset_sum (T U : Finset I) (hTU : Disjoint T U) (f : Finset I → ℝ) :
    (∑ C ∈ (T ∪ U).powerset, f C) = ∑ A ∈ T.powerset, ∑ B ∈ U.powerset, f (A ∪ B) := by
  rw [← Finset.sum_product T.powerset U.powerset (fun p : Finset I × Finset I => f (p.1 ∪ p.2))]
  apply Finset.sum_bij' (fun C _ => (C ∩ T, C ∩ U)) (fun p _ => p.1 ∪ p.2)
  · intro C _
    exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
      Finset.mem_powerset.mpr Finset.inter_subset_right⟩
  · intro p hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    exact Finset.mem_powerset.mpr (Finset.union_subset_union
      (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB))
  · intro C hC
    have hsub := Finset.mem_powerset.mp hC
    ext i
    have hi : i ∈ C → i ∈ T ∨ i ∈ U := fun h => Finset.mem_union.mp (hsub h)
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  · intro p hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    have hAsub := Finset.mem_powerset.mp hA
    have hBsub := Finset.mem_powerset.mp hB
    apply Prod.ext <;> ext i
    · have hAi : i ∈ p.1 → i ∈ T := fun h => hAsub h
      have hBi : i ∈ p.2 → i ∈ U := fun h => hBsub h
      have hdis : ¬(i ∈ T ∧ i ∈ U) := fun h => Finset.disjoint_left.mp hTU h.1 h.2
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    · have hAi : i ∈ p.1 → i ∈ T := fun h => hAsub h
      have hBi : i ∈ p.2 → i ∈ U := fun h => hBsub h
      have hdis : ¬(i ∈ T ∧ i ∈ U) := fun h => Finset.disjoint_left.mp hTU h.1 h.2
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
  · intro C hC
    congr 1
    have hsub := Finset.mem_powerset.mp hC
    ext i
    have hi : i ∈ C → i ∈ T ∨ i ∈ U := fun h => Finset.mem_union.mp (hsub h)
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto

end Erdos3

end

end OAI
