module
public import M6.Source.AXCons
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Source.MPCons
private theorem pop_row0 : resolveAt exactSites 3844 = some (UnpairPartial.expected 3844 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row1 : resolveAt exactSites 3845 = some (UnpairPartial.expected 3844 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row2 : resolveAt exactSites 3846 = some (UnpairPartial.expected 3844 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row3 : resolveAt exactSites 3847 = some (UnpairPartial.expected 3844 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row4 : resolveAt exactSites 3848 = some (UnpairPartial.expected 3844 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row5 : resolveAt exactSites 3849 = some (UnpairPartial.expected 3844 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row6 : resolveAt exactSites 3850 = some (UnpairPartial.expected 3844 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row7 : resolveAt exactSites 3851 = some (UnpairPartial.expected 3844 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row8 : resolveAt exactSites 3852 = some (UnpairPartial.expected 3844 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row9 : resolveAt exactSites 3853 = some (UnpairPartial.expected 3844 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pop_row10 : resolveAt exactSites 3854 = some (UnpairPartial.expected 3844 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem pop_bound : UnpairPartial.Bound exactSites 3844 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pop_row0
  · exact pop_row1
  · exact pop_row2
  · exact pop_row3
  · exact pop_row4
  · exact pop_row5
  · exact pop_row6
  · exact pop_row7
  · exact pop_row8
  · exact pop_row9
  · exact pop_row10
private theorem pair_row0 : resolveAt exactSites 3855 = some (AXPair.relocate 3824 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pair_row1 : resolveAt exactSites 3856 = some (AXPair.relocate 3824 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pair_row2 : resolveAt exactSites 3857 = some (AXPair.relocate 3824 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pair_row3 : resolveAt exactSites 3858 = some (AXPair.relocate 3824 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pair_row4 : resolveAt exactSites 3859 = some (AXPair.relocate 3824 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pair_row5 : resolveAt exactSites 3860 = some (AXPair.relocate 3824 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pair_row6 : resolveAt exactSites 3861 = some (AXPair.relocate 3824 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pair_row7 : resolveAt exactSites 3862 = some (AXPair.relocate 3824 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pair_row8 : resolveAt exactSites 3863 = some (AXPair.relocate 3824 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem pair_row9 : resolveAt exactSites 3864 = some (AXPair.relocate 3824 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem pair_bound : AXPair.Bound exactSites 3824 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_row0
  · exact pair_row1
  · exact pair_row2
  · exact pair_row3
  · exact pair_row4
  · exact pair_row5
  · exact pair_row6
  · exact pair_row7
  · exact pair_row8
  · exact pair_row9
private theorem times_row0 : resolveAt exactSites 3865 = some (AXTimes4.expected 3865 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem times_row1 : resolveAt exactSites 3866 = some (AXTimes4.expected 3865 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem times_row2 : resolveAt exactSites 3867 = some (AXTimes4.expected 3865 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem times_row3 : resolveAt exactSites 3868 = some (AXTimes4.expected 3865 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem times_row4 : resolveAt exactSites 3869 = some (AXTimes4.expected 3865 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem times_row5 : resolveAt exactSites 3870 = some (AXTimes4.expected 3865 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem times_bound : AXTimes4.Bound exactSites 3865 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact times_row0
  · exact times_row1
  · exact times_row2
  · exact times_row3
  · exact times_row4
  · exact times_row5

/-- Actual MP implication construction: pop the antecedent from W and construct
its implication into T, preserving all non-scratch registers. -/
theorem cons (t w : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n
      ⟨.at 3844,AXPush.registers ⟨t,w,0,0,f⟩⟩
      ⟨.at 3871,AXPush.registers
        ⟨AXCode.wim (Cantor.decode w).1 t,(Cantor.decode w).2,0,0,f⟩⟩ :=
  AXCons.cons pop_bound pair_bound times_bound t w f
#print axioms cons
end M6.Source.MPCons

