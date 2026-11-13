import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactConcreteMask
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74ShortDefect
open Finset CompactListMask CompactConcreteMask CompactHighPopulation
open CompactSymbolicPorts
open scoped BigOperators
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
def B : ℕ := 2^67
def smallDefect : List ℕ := (List.range 3297).map (defect 1063 support)
theorem support_short : support ⊆ Finset.range 3297 := by
  intro j hj
  simp only [support, Finset.mem_sdiff, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hj ⊢
  omega

theorem defect_sum_short :
    (∑ j ∈ Finset.range 3297, defect 1063 support j * B^j) =
    ∑ j ∈ Finset.range 8807, defect 1063 support j * B^j := by
  apply Finset.sum_subset (Finset.range_mono (by decide : 3297≤8807))
  intro j _ hj
  have hge : 3297≤j := by simpa only [Finset.mem_range,not_lt] using hj
  have hs : j∉support := by
    intro hm
    have hm' := support_short hm
    simp only [Finset.mem_range] at hm'
    omega
  have hn : j≠1063 := by omega
  simp [defect,hn,hs]

theorem low_plus_defect : lowNat + Nat.ofDigits B smallDefect + 1 = B^8807 := by
  have h := digits_add_defect B 8807 1063 support (by norm_num [B])
  rw [← defect_sum_short, ← ofDigits_map_range B (defect 1063 support) 3297] at h
  exact h

theorem defect_lt : Nat.ofDigits B smallDefect < B^3297 := by
  have hd : ∀ x ∈ smallDefect, x<B := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    unfold defect
    split_ifs <;> norm_num [B]
  have h := Nat.ofDigits_lt_base_pow_length (show 1<B by norm_num [B]) hd
  simpa only [smallDefect,List.length_map,List.length_range] using h


#print axioms Trace74ShortDefect.low_plus_defect
#print axioms Trace74ShortDefect.defect_lt
end Trace74ShortDefect
