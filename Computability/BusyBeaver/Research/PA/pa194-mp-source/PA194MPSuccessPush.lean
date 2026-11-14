import M6.Source.AXPushParam
import PA194SourceProgram
/-! Arithmetic proof adapted from M6.Source.MPSuccessPush; every literal
source binding is reproved against the PA194 program. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA194MPSource.MPSuccessPush
open M6.Source

private theorem row0 : resolveAt PA194SourceProgram.sites 3634 =
    some (AXPushParam.relocate 3609 (AXPush.expected 0)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row1 : resolveAt PA194SourceProgram.sites 3635 =
    some (AXPushParam.relocate 3609 (AXPush.expected 1)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row2 : resolveAt PA194SourceProgram.sites 3636 =
    some (AXPushParam.relocate 3609 (AXPush.expected 2)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3 : resolveAt PA194SourceProgram.sites 3637 =
    some (AXPushParam.relocate 3609 (AXPush.expected 3)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row4 : resolveAt PA194SourceProgram.sites 3638 =
    some (AXPushParam.relocate 3609 (AXPush.expected 4)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row5 : resolveAt PA194SourceProgram.sites 3639 =
    some (AXPushParam.relocate 3609 (AXPush.expected 5)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row6 : resolveAt PA194SourceProgram.sites 3640 =
    some (AXPushParam.relocate 3609 (AXPush.expected 6)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row7 : resolveAt PA194SourceProgram.sites 3641 =
    some (AXPushParam.relocate 3609 (AXPush.expected 7)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row8 : resolveAt PA194SourceProgram.sites 3642 =
    some (AXPushParam.relocate 3609 (AXPush.expected 8)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row9 : resolveAt PA194SourceProgram.sites 3643 =
    some (AXPushParam.relocate 3609 (AXPush.expected 9)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row10 : resolveAt PA194SourceProgram.sites 3644 =
    some (AXPushParam.relocate 3609 (AXPush.expected 10)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row11 : resolveAt PA194SourceProgram.sites 3645 =
    some (AXPushParam.relocate 3609 (AXPush.expected 11)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row12 : resolveAt PA194SourceProgram.sites 3646 =
    some (AXPushParam.relocate 3609 (AXPush.expected 12)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row13 : resolveAt PA194SourceProgram.sites 3647 =
    some (AXPushParam.relocate 3609 (AXPush.expected 13)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row14 : resolveAt PA194SourceProgram.sites 3648 =
    some (AXPushParam.relocate 3609 (AXPush.expected 14)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row15 : resolveAt PA194SourceProgram.sites 3649 =
    some (AXPushParam.relocate 3609 (AXPush.expected 15)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row16 : resolveAt PA194SourceProgram.sites 3650 =
    some (AXPushParam.relocate 3609 (AXPush.expected 16)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row17 : resolveAt PA194SourceProgram.sites 3651 =
    some (AXPushParam.relocate 3609 (AXPush.expected 17)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row18 : resolveAt PA194SourceProgram.sites 3652 =
    some (AXPushParam.relocate 3609 (AXPush.expected 18)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl

theorem bound : AXPushParam.Bound PA194SourceProgram.sites 3609 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18

/-- Actual MP success push at3634–3652. The entire unrelated register frame is preserved. -/
theorem push (t w : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps PA194SourceProgram.sites n
      ⟨.at 3634,AXPush.registers ⟨t,w,0,0,f⟩⟩
      ⟨.at 3653,AXPush.registers ⟨0,Cantor.pair t w,0,0,f⟩⟩ := by
  exact AXPushParam.push bound t w f

#print axioms bound
#print axioms push
end PA194MPSource.MPSuccessPush

