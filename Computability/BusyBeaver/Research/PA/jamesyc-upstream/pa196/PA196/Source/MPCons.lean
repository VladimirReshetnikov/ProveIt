module
public import M6.Source.AXCons
public import PA196.Program
/-! Arithmetic proof adapted from M6.Source.MPCons; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA196.Source.MPCons
open M6.Source
private theorem pop_row0 : resolveAt Program.sites 3733 = some (UnpairPartial.expected 3733 0) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row1 : resolveAt Program.sites 3734 = some (UnpairPartial.expected 3733 1) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row2 : resolveAt Program.sites 3735 = some (UnpairPartial.expected 3733 2) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row3 : resolveAt Program.sites 3736 = some (UnpairPartial.expected 3733 3) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row4 : resolveAt Program.sites 3737 = some (UnpairPartial.expected 3733 4) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row5 : resolveAt Program.sites 3738 = some (UnpairPartial.expected 3733 5) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row6 : resolveAt Program.sites 3739 = some (UnpairPartial.expected 3733 6) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row7 : resolveAt Program.sites 3740 = some (UnpairPartial.expected 3733 7) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row8 : resolveAt Program.sites 3741 = some (UnpairPartial.expected 3733 8) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row9 : resolveAt Program.sites 3742 = some (UnpairPartial.expected 3733 9) := by
  rw [Program.resolve_tree]
  rfl
private theorem pop_row10 : resolveAt Program.sites 3743 = some (UnpairPartial.expected 3733 10) := by
  rw [Program.resolve_tree]
  rfl
theorem pop_bound : UnpairPartial.Bound Program.sites 3733 := by
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
private theorem pair_row0 : resolveAt Program.sites 3744 = some (AXPair.relocate 3713 (AXPair.expected 6)) := by
  rw [Program.resolve_tree]
  rfl
private theorem pair_row1 : resolveAt Program.sites 3745 = some (AXPair.relocate 3713 (AXPair.expected 7)) := by
  rw [Program.resolve_tree]
  rfl
private theorem pair_row2 : resolveAt Program.sites 3746 = some (AXPair.relocate 3713 (AXPair.expected 8)) := by
  rw [Program.resolve_tree]
  rfl
private theorem pair_row3 : resolveAt Program.sites 3747 = some (AXPair.relocate 3713 (AXPair.expected 9)) := by
  rw [Program.resolve_tree]
  rfl
private theorem pair_row4 : resolveAt Program.sites 3748 = some (AXPair.relocate 3713 (AXPair.expected 10)) := by
  rw [Program.resolve_tree]
  rfl
private theorem pair_row5 : resolveAt Program.sites 3749 = some (AXPair.relocate 3713 (AXPair.expected 11)) := by
  rw [Program.resolve_tree]
  rfl
private theorem pair_row6 : resolveAt Program.sites 3750 = some (AXPair.relocate 3713 (AXPair.expected 12)) := by
  rw [Program.resolve_tree]
  rfl
private theorem pair_row7 : resolveAt Program.sites 3751 = some (AXPair.relocate 3713 (AXPair.expected 13)) := by
  rw [Program.resolve_tree]
  rfl
private theorem pair_row8 : resolveAt Program.sites 3752 = some (AXPair.relocate 3713 (AXPair.expected 14)) := by
  rw [Program.resolve_tree]
  rfl
private theorem pair_row9 : resolveAt Program.sites 3753 = some (AXPair.relocate 3713 (AXPair.expected 15)) := by
  rw [Program.resolve_tree]
  rfl
theorem pair_bound : AXPair.Bound Program.sites 3713 := by
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
private theorem times_row0 : resolveAt Program.sites 3754 = some (AXTimes4.expected 3754 0) := by
  rw [Program.resolve_tree]
  rfl
private theorem times_row1 : resolveAt Program.sites 3755 = some (AXTimes4.expected 3754 1) := by
  rw [Program.resolve_tree]
  rfl
private theorem times_row2 : resolveAt Program.sites 3756 = some (AXTimes4.expected 3754 2) := by
  rw [Program.resolve_tree]
  rfl
private theorem times_row3 : resolveAt Program.sites 3757 = some (AXTimes4.expected 3754 3) := by
  rw [Program.resolve_tree]
  rfl
private theorem times_row4 : resolveAt Program.sites 3758 = some (AXTimes4.expected 3754 4) := by
  rw [Program.resolve_tree]
  rfl
private theorem times_row5 : resolveAt Program.sites 3759 = some (AXTimes4.expected 3754 5) := by
  rw [Program.resolve_tree]
  rfl
theorem times_bound : AXTimes4.Bound Program.sites 3754 := by
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
    ∃ n, 0 < n ∧ Steps Program.sites n
      ⟨.at 3733,AXPush.registers ⟨t,w,0,0,f⟩⟩
      ⟨.at 3760,AXPush.registers
        ⟨AXCode.wim (Cantor.decode w).1 t,(Cantor.decode w).2,0,0,f⟩⟩ :=
  AXCons.cons pop_bound pair_bound times_bound t w f
#print axioms cons
end PA196.Source.MPCons

