import M6.Source.AXGateCompare
import PA194SourceProgram
/-! Arithmetic proof adapted from the corresponding M6 module.
The row bindings are rechecked against the PA194 tree. -/
set_option maxRecDepth 100000
namespace PA194AXGateCompare
open M6.Source M6.Source.AXGateCompare
private theorem row3523_0 : resolveAt PA194SourceProgram.sites 3523 = some (expected 3523 0) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_1 : resolveAt PA194SourceProgram.sites 3524 = some (expected 3523 1) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_2 : resolveAt PA194SourceProgram.sites 3525 = some (expected 3523 2) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_3 : resolveAt PA194SourceProgram.sites 3526 = some (expected 3523 3) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_4 : resolveAt PA194SourceProgram.sites 3527 = some (expected 3523 4) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_5 : resolveAt PA194SourceProgram.sites 3528 = some (expected 3523 5) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_6 : resolveAt PA194SourceProgram.sites 3529 = some (expected 3523 6) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_7 : resolveAt PA194SourceProgram.sites 3530 = some (expected 3523 7) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_8 : resolveAt PA194SourceProgram.sites 3531 = some (expected 3523 8) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_9 : resolveAt PA194SourceProgram.sites 3532 = some (expected 3523 9) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_10 : resolveAt PA194SourceProgram.sites 3533 = some (expected 3523 10) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3523_11 : resolveAt PA194SourceProgram.sites 3534 = some (expected 3523 11) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem bound3523 : Bound PA194SourceProgram.sites 3523 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3523_0
  · exact row3523_1
  · exact row3523_2
  · exact row3523_3
  · exact row3523_4
  · exact row3523_5
  · exact row3523_6
  · exact row3523_7
  · exact row3523_8
  · exact row3523_9
  · exact row3523_10
  · exact row3523_11
theorem compare3523 (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps PA194SourceProgram.sites n (configAt 3523 0 ⟨t,h,x,f⟩)
      (configAt 3523 12 ⟨if h=x then 0 else t,0,0,f⟩) :=
  compare bound3523 t h x f
#print axioms compare3523
private theorem row3541_0 : resolveAt PA194SourceProgram.sites 3541 = some (expected 3541 0) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_1 : resolveAt PA194SourceProgram.sites 3542 = some (expected 3541 1) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_2 : resolveAt PA194SourceProgram.sites 3543 = some (expected 3541 2) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_3 : resolveAt PA194SourceProgram.sites 3544 = some (expected 3541 3) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_4 : resolveAt PA194SourceProgram.sites 3545 = some (expected 3541 4) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_5 : resolveAt PA194SourceProgram.sites 3546 = some (expected 3541 5) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_6 : resolveAt PA194SourceProgram.sites 3547 = some (expected 3541 6) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_7 : resolveAt PA194SourceProgram.sites 3548 = some (expected 3541 7) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_8 : resolveAt PA194SourceProgram.sites 3549 = some (expected 3541 8) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_9 : resolveAt PA194SourceProgram.sites 3550 = some (expected 3541 9) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_10 : resolveAt PA194SourceProgram.sites 3551 = some (expected 3541 10) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
private theorem row3541_11 : resolveAt PA194SourceProgram.sites 3552 = some (expected 3541 11) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem bound3541 : Bound PA194SourceProgram.sites 3541 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3541_0
  · exact row3541_1
  · exact row3541_2
  · exact row3541_3
  · exact row3541_4
  · exact row3541_5
  · exact row3541_6
  · exact row3541_7
  · exact row3541_8
  · exact row3541_9
  · exact row3541_10
  · exact row3541_11
theorem compare3541 (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps PA194SourceProgram.sites n (configAt 3541 0 ⟨t,h,x,f⟩)
      (configAt 3541 12 ⟨if h=x then 0 else t,0,0,f⟩) :=
  compare bound3541 t h x f
#print axioms compare3541
end PA194AXGateCompare

