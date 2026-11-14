import M6.Source.CopyToT
import PA194SourceProgram
import PA194SourceProgram
/-! Arithmetic proof adapted from M6.Source.MPCopy; every literal
source binding is reproved against the PA194 program. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA194MPSource.MPCopy
open M6.Source
private theorem first_row0 : resolveAt PA194SourceProgram.sites 3587 = some (CopyToT.expected 4 3587 0) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem first_row1 : resolveAt PA194SourceProgram.sites 3588 = some (CopyToT.expected 4 3587 1) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem first_row2 : resolveAt PA194SourceProgram.sites 3589 = some (CopyToT.expected 4 3587 2) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem first_row3 : resolveAt PA194SourceProgram.sites 3590 = some (CopyToT.expected 4 3587 3) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem first_row4 : resolveAt PA194SourceProgram.sites 3591 = some (CopyToT.expected 4 3587 4) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem first_row5 : resolveAt PA194SourceProgram.sites 3592 = some (CopyToT.expected 4 3587 5) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem first_row6 : resolveAt PA194SourceProgram.sites 3593 = some (CopyToT.expected 4 3587 6) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem first_bound : CopyToT.Bound PA194SourceProgram.sites 4 3587 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact first_row0
  · exact first_row1
  · exact first_row2
  · exact first_row3
  · exact first_row4
  · exact first_row5
  · exact first_row6
theorem first_copy (d t : Nat) (f : Registers) :
    Steps PA194SourceProgram.sites (7*d+2) (CopyToT.config 4 3587 0 d t 0 f)
      (CopyToT.config 4 3587 7 d (t+d) 0 f) :=
  CopyToT.copy (by decide) (by decide) first_bound d t f
#print axioms first_copy
private theorem last_row0 : resolveAt PA194SourceProgram.sites 3653 = some (CopyToT.expected 4 3653 0) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem last_row1 : resolveAt PA194SourceProgram.sites 3654 = some (CopyToT.expected 4 3653 1) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem last_row2 : resolveAt PA194SourceProgram.sites 3655 = some (CopyToT.expected 4 3653 2) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem last_row3 : resolveAt PA194SourceProgram.sites 3656 = some (CopyToT.expected 4 3653 3) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem last_row4 : resolveAt PA194SourceProgram.sites 3657 = some (CopyToT.expected 4 3653 4) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem last_row5 : resolveAt PA194SourceProgram.sites 3658 = some (CopyToT.expected 4 3653 5) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem last_row6 : resolveAt PA194SourceProgram.sites 3659 = some (CopyToT.expected 4 3653 6) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem last_bound : CopyToT.Bound PA194SourceProgram.sites 4 3653 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact last_row0
  · exact last_row1
  · exact last_row2
  · exact last_row3
  · exact last_row4
  · exact last_row5
  · exact last_row6
theorem last_copy (d t : Nat) (f : Registers) :
    Steps PA194SourceProgram.sites (7*d+2) (CopyToT.config 4 3653 0 d t 0 f)
      (CopyToT.config 4 3653 7 d (t+d) 0 f) :=
  CopyToT.copy (by decide) (by decide) last_bound d t f
#print axioms last_copy
end PA194MPSource.MPCopy

