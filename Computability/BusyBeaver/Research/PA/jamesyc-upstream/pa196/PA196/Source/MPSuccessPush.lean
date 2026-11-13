module
public import M6.Source.AXPushParam
public import PA196.Program
/-! Arithmetic proof adapted from M6.Source.MPSuccessPush; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA196.Source.MPSuccessPush
open M6.Source

private theorem row0 : resolveAt Program.sites 3773 =
    some (AXPushParam.relocate 3748 (AXPush.expected 0)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row1 : resolveAt Program.sites 3774 =
    some (AXPushParam.relocate 3748 (AXPush.expected 1)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row2 : resolveAt Program.sites 3775 =
    some (AXPushParam.relocate 3748 (AXPush.expected 2)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3 : resolveAt Program.sites 3776 =
    some (AXPushParam.relocate 3748 (AXPush.expected 3)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row4 : resolveAt Program.sites 3777 =
    some (AXPushParam.relocate 3748 (AXPush.expected 4)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row5 : resolveAt Program.sites 3778 =
    some (AXPushParam.relocate 3748 (AXPush.expected 5)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row6 : resolveAt Program.sites 3779 =
    some (AXPushParam.relocate 3748 (AXPush.expected 6)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row7 : resolveAt Program.sites 3780 =
    some (AXPushParam.relocate 3748 (AXPush.expected 7)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row8 : resolveAt Program.sites 3781 =
    some (AXPushParam.relocate 3748 (AXPush.expected 8)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row9 : resolveAt Program.sites 3782 =
    some (AXPushParam.relocate 3748 (AXPush.expected 9)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row10 : resolveAt Program.sites 3783 =
    some (AXPushParam.relocate 3748 (AXPush.expected 10)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row11 : resolveAt Program.sites 3784 =
    some (AXPushParam.relocate 3748 (AXPush.expected 11)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row12 : resolveAt Program.sites 3785 =
    some (AXPushParam.relocate 3748 (AXPush.expected 12)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row13 : resolveAt Program.sites 3786 =
    some (AXPushParam.relocate 3748 (AXPush.expected 13)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row14 : resolveAt Program.sites 3787 =
    some (AXPushParam.relocate 3748 (AXPush.expected 14)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row15 : resolveAt Program.sites 3788 =
    some (AXPushParam.relocate 3748 (AXPush.expected 15)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row16 : resolveAt Program.sites 3789 =
    some (AXPushParam.relocate 3748 (AXPush.expected 16)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row17 : resolveAt Program.sites 3790 =
    some (AXPushParam.relocate 3748 (AXPush.expected 17)) := by
  rw [Program.resolve_tree]
  rfl
private theorem row18 : resolveAt Program.sites 3791 =
    some (AXPushParam.relocate 3748 (AXPush.expected 18)) := by
  rw [Program.resolve_tree]
  rfl

theorem bound : AXPushParam.Bound Program.sites 3748 := by
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

/-- Actual MP success push at3773–3791. The entire unrelated register frame is preserved. -/
theorem push (t w : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps Program.sites n
      ⟨.at 3773,AXPush.registers ⟨t,w,0,0,f⟩⟩
      ⟨.at 3792,AXPush.registers ⟨0,Cantor.pair t w,0,0,f⟩⟩ := by
  exact AXPushParam.push bound t w f

#print axioms bound
#print axioms push
end PA196.Source.MPSuccessPush

