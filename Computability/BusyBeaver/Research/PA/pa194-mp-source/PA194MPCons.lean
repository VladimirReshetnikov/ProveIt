import M6.Source.AXCons
import PA194SourceProgram
/-! Arithmetic proof adapted from M6.Source.MPCons; every literal
source binding is reproved against the PA194 program. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA194MPSource.MPCons
open M6.Source
private theorem pop_row0 : resolveAt PA194SourceProgram.sites 3594 = some (UnpairPartial.expected 3594 0) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row1 : resolveAt PA194SourceProgram.sites 3595 = some (UnpairPartial.expected 3594 1) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row2 : resolveAt PA194SourceProgram.sites 3596 = some (UnpairPartial.expected 3594 2) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row3 : resolveAt PA194SourceProgram.sites 3597 = some (UnpairPartial.expected 3594 3) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row4 : resolveAt PA194SourceProgram.sites 3598 = some (UnpairPartial.expected 3594 4) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row5 : resolveAt PA194SourceProgram.sites 3599 = some (UnpairPartial.expected 3594 5) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row6 : resolveAt PA194SourceProgram.sites 3600 = some (UnpairPartial.expected 3594 6) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row7 : resolveAt PA194SourceProgram.sites 3601 = some (UnpairPartial.expected 3594 7) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row8 : resolveAt PA194SourceProgram.sites 3602 = some (UnpairPartial.expected 3594 8) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row9 : resolveAt PA194SourceProgram.sites 3603 = some (UnpairPartial.expected 3594 9) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pop_row10 : resolveAt PA194SourceProgram.sites 3604 = some (UnpairPartial.expected 3594 10) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem pop_bound : UnpairPartial.Bound PA194SourceProgram.sites 3594 := by
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
private theorem pair_row0 : resolveAt PA194SourceProgram.sites 3605 = some (AXPair.relocate 3574 (AXPair.expected 6)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pair_row1 : resolveAt PA194SourceProgram.sites 3606 = some (AXPair.relocate 3574 (AXPair.expected 7)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pair_row2 : resolveAt PA194SourceProgram.sites 3607 = some (AXPair.relocate 3574 (AXPair.expected 8)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pair_row3 : resolveAt PA194SourceProgram.sites 3608 = some (AXPair.relocate 3574 (AXPair.expected 9)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pair_row4 : resolveAt PA194SourceProgram.sites 3609 = some (AXPair.relocate 3574 (AXPair.expected 10)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pair_row5 : resolveAt PA194SourceProgram.sites 3610 = some (AXPair.relocate 3574 (AXPair.expected 11)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pair_row6 : resolveAt PA194SourceProgram.sites 3611 = some (AXPair.relocate 3574 (AXPair.expected 12)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pair_row7 : resolveAt PA194SourceProgram.sites 3612 = some (AXPair.relocate 3574 (AXPair.expected 13)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pair_row8 : resolveAt PA194SourceProgram.sites 3613 = some (AXPair.relocate 3574 (AXPair.expected 14)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem pair_row9 : resolveAt PA194SourceProgram.sites 3614 = some (AXPair.relocate 3574 (AXPair.expected 15)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem pair_bound : AXPair.Bound PA194SourceProgram.sites 3574 := by
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
private theorem times_row0 : resolveAt PA194SourceProgram.sites 3615 = some (AXTimes4.expected 3615 0) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem times_row1 : resolveAt PA194SourceProgram.sites 3616 = some (AXTimes4.expected 3615 1) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem times_row2 : resolveAt PA194SourceProgram.sites 3617 = some (AXTimes4.expected 3615 2) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem times_row3 : resolveAt PA194SourceProgram.sites 3618 = some (AXTimes4.expected 3615 3) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem times_row4 : resolveAt PA194SourceProgram.sites 3619 = some (AXTimes4.expected 3615 4) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem times_row5 : resolveAt PA194SourceProgram.sites 3620 = some (AXTimes4.expected 3615 5) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem times_bound : AXTimes4.Bound PA194SourceProgram.sites 3615 := by
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
    ∃ n, 0 < n ∧ Steps PA194SourceProgram.sites n
      ⟨.at 3594,AXPush.registers ⟨t,w,0,0,f⟩⟩
      ⟨.at 3621,AXPush.registers
        ⟨AXCode.wim (Cantor.decode w).1 t,(Cantor.decode w).2,0,0,f⟩⟩ :=
  AXCons.cons pop_bound pair_bound times_bound t w f
#print axioms cons
end PA194MPSource.MPCons

