module
public import M6.Source.CopyToT
public import PA196.Program
public import PA196.Program
/-! Arithmetic proof adapted from M6.Source.MPCopy; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA196.Source.MPCopy
open M6.Source
private theorem first_row0 : resolveAt Program.sites 3726 = some (CopyToT.expected 4 3726 0) := by
  rw [Program.resolve_tree]
  rfl
private theorem first_row1 : resolveAt Program.sites 3727 = some (CopyToT.expected 4 3726 1) := by
  rw [Program.resolve_tree]
  rfl
private theorem first_row2 : resolveAt Program.sites 3728 = some (CopyToT.expected 4 3726 2) := by
  rw [Program.resolve_tree]
  rfl
private theorem first_row3 : resolveAt Program.sites 3729 = some (CopyToT.expected 4 3726 3) := by
  rw [Program.resolve_tree]
  rfl
private theorem first_row4 : resolveAt Program.sites 3730 = some (CopyToT.expected 4 3726 4) := by
  rw [Program.resolve_tree]
  rfl
private theorem first_row5 : resolveAt Program.sites 3731 = some (CopyToT.expected 4 3726 5) := by
  rw [Program.resolve_tree]
  rfl
private theorem first_row6 : resolveAt Program.sites 3732 = some (CopyToT.expected 4 3726 6) := by
  rw [Program.resolve_tree]
  rfl
theorem first_bound : CopyToT.Bound Program.sites 4 3726 := by
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
    Steps Program.sites (7*d+2) (CopyToT.config 4 3726 0 d t 0 f)
      (CopyToT.config 4 3726 7 d (t+d) 0 f) :=
  CopyToT.copy (by decide) (by decide) first_bound d t f
#print axioms first_copy
private theorem last_row0 : resolveAt Program.sites 3792 = some (CopyToT.expected 4 3792 0) := by
  rw [Program.resolve_tree]
  rfl
private theorem last_row1 : resolveAt Program.sites 3793 = some (CopyToT.expected 4 3792 1) := by
  rw [Program.resolve_tree]
  rfl
private theorem last_row2 : resolveAt Program.sites 3794 = some (CopyToT.expected 4 3792 2) := by
  rw [Program.resolve_tree]
  rfl
private theorem last_row3 : resolveAt Program.sites 3795 = some (CopyToT.expected 4 3792 3) := by
  rw [Program.resolve_tree]
  rfl
private theorem last_row4 : resolveAt Program.sites 3796 = some (CopyToT.expected 4 3792 4) := by
  rw [Program.resolve_tree]
  rfl
private theorem last_row5 : resolveAt Program.sites 3797 = some (CopyToT.expected 4 3792 5) := by
  rw [Program.resolve_tree]
  rfl
private theorem last_row6 : resolveAt Program.sites 3798 = some (CopyToT.expected 4 3792 6) := by
  rw [Program.resolve_tree]
  rfl
theorem last_bound : CopyToT.Bound Program.sites 4 3792 := by
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
    Steps Program.sites (7*d+2) (CopyToT.config 4 3792 0 d t 0 f)
      (CopyToT.config 4 3792 7 d (t+d) 0 f) :=
  CopyToT.copy (by decide) (by decide) last_bound d t f
#print axioms last_copy
end PA196.Source.MPCopy

