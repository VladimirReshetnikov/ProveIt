import DiophantineConsistency.NativeVariableMask
import DiophantineConsistency.NativeWordPopulation

/-! # Exact population of a variable-capacity low mask -/

namespace DiophantineConsistency.NativeVariablePopulation

open NativeVariableMask Jones1982
open scoped BigOperators

private theorem sum_support {L : ℕ} (S : Finset ℕ) (hS : ∀ j ∈ S, j < L) :
    (∑ j ∈ Finset.range L, if j ∈ S then (1 : ℕ) else 0) = S.card := by
  classical
  have he : (Finset.range L).filter (fun j => j ∈ S) = S := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨And.right,fun hj => ⟨hS j hj,hj⟩⟩
  rw [← Finset.sum_filter,he]
  simp

/-- Each support position clears one bit and the distinguished dummy
clears one additional bit. -/
theorem capacity_sum {L : ℕ} (S : Finset ℕ) (hS : ∀ j ∈ S, j < L)
    {dummy : ℕ} (hd : dummy ∈ S) :
    (∑ j ∈ Finset.range L, capacity S dummy j) = S.card + 1 := by
  classical
  have he (j : ℕ) : capacity S dummy j =
      (if j ∈ S then 1 else 0) + if j = dummy then 1 else 0 := by
    unfold capacity
    by_cases hj : j = dummy
    · subst j; simp [hd]
    · simp [hj]
  simp_rw [he]
  rw [Finset.sum_add_distrib,sum_support S hS]
  simp only [Finset.sum_ite_eq',Finset.mem_range,if_pos (hS dummy hd)]

/-- Exact population balance, without evaluating the word or its radix
power. All finite-word arithmetic is proved at an arbitrary cell length. -/
theorem cell_population {v L : ℕ} (hv : 2 ≤ v) (S : Finset ℕ)
    (hS : ∀ j ∈ S, j < L) {dummy : ℕ} (hd : dummy ∈ S) :
    σ 2 (cellWord (2^v) L S dummy) + S.card + 1 = L*v := by
  classical
  have hb (j : ℕ) : capacity S dummy j ≤ v := le_trans (capacity_le_two S dummy j) hv
  have hl (j : ℕ) : cellDigit (2^v) S dummy j < 2^v := by
    unfold cellDigit
    have hh : 0 < 2 ^ capacity S dummy j := by positivity
    have hp : 0 < 2^v := by positivity
    omega
  have hword : Nat.ofDigits (2^v) ((List.range L).map (cellDigit (2^v) S dummy)) =
      cellWord (2^v) L S dummy := by
    rw [Jones1982.ofDigits_map_range]
    rfl
  have hpop := MaskPopulation.population_ofDigits v
    ((List.range L).map (cellDigit (2^v) S dummy)) (by
      intro x hx
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
      exact hl j)
  rw [hword,List.map_map] at hpop
  rw [← List.sum_toFinset _ (show (List.range L).Nodup from List.nodup_range)] at hpop
  simp only [List.toFinset_range,Function.comp_apply] at hpop
  have he (j : ℕ) : σ 2 (cellDigit (2^v) S dummy j) + capacity S dummy j = v := by
    unfold cellDigit
    rw [MaskPopulation.population_pow_sub_pow (hb j),Nat.sub_add_cancel (hb j)]
  have hs : (∑ j ∈ Finset.range L,
      (σ 2 (cellDigit (2^v) S dummy j) + capacity S dummy j)) = L*v := by
    simp_rw [he]
    simp
  rw [Finset.sum_add_distrib,capacity_sum S hS hd,← hpop] at hs
  omega

end DiophantineConsistency.NativeVariablePopulation
