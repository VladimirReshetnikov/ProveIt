module
public import M6.Source.AXGateCompare
public import PA196.Program
/-! Arithmetic proof adapted from the corresponding M6 module.
All source-row bindings below refer to the PA196 tree. -/
@[expose] public section
set_option maxRecDepth 100000
namespace PA196.Source.AXGateCompare
open M6.Source M6.Source.AXGateCompare
private theorem row3662_0 : resolveAt Program.sites 3662 = some (expected 3662 0) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_1 : resolveAt Program.sites 3663 = some (expected 3662 1) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_2 : resolveAt Program.sites 3664 = some (expected 3662 2) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_3 : resolveAt Program.sites 3665 = some (expected 3662 3) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_4 : resolveAt Program.sites 3666 = some (expected 3662 4) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_5 : resolveAt Program.sites 3667 = some (expected 3662 5) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_6 : resolveAt Program.sites 3668 = some (expected 3662 6) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_7 : resolveAt Program.sites 3669 = some (expected 3662 7) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_8 : resolveAt Program.sites 3670 = some (expected 3662 8) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_9 : resolveAt Program.sites 3671 = some (expected 3662 9) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_10 : resolveAt Program.sites 3672 = some (expected 3662 10) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3662_11 : resolveAt Program.sites 3673 = some (expected 3662 11) := by
  rw [Program.resolve_tree]
  rfl
theorem bound3662 : Bound Program.sites 3662 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3662_0
  · exact row3662_1
  · exact row3662_2
  · exact row3662_3
  · exact row3662_4
  · exact row3662_5
  · exact row3662_6
  · exact row3662_7
  · exact row3662_8
  · exact row3662_9
  · exact row3662_10
  · exact row3662_11
theorem compare3662 (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps Program.sites n (configAt 3662 0 ⟨t,h,x,f⟩)
      (configAt 3662 12 ⟨if h=x then 0 else t,0,0,f⟩) :=
  compare bound3662 t h x f
#print axioms compare3662
private theorem row3680_0 : resolveAt Program.sites 3680 = some (expected 3680 0) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_1 : resolveAt Program.sites 3681 = some (expected 3680 1) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_2 : resolveAt Program.sites 3682 = some (expected 3680 2) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_3 : resolveAt Program.sites 3683 = some (expected 3680 3) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_4 : resolveAt Program.sites 3684 = some (expected 3680 4) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_5 : resolveAt Program.sites 3685 = some (expected 3680 5) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_6 : resolveAt Program.sites 3686 = some (expected 3680 6) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_7 : resolveAt Program.sites 3687 = some (expected 3680 7) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_8 : resolveAt Program.sites 3688 = some (expected 3680 8) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_9 : resolveAt Program.sites 3689 = some (expected 3680 9) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_10 : resolveAt Program.sites 3690 = some (expected 3680 10) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3680_11 : resolveAt Program.sites 3691 = some (expected 3680 11) := by
  rw [Program.resolve_tree]
  rfl
theorem bound3680 : Bound Program.sites 3680 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3680_0
  · exact row3680_1
  · exact row3680_2
  · exact row3680_3
  · exact row3680_4
  · exact row3680_5
  · exact row3680_6
  · exact row3680_7
  · exact row3680_8
  · exact row3680_9
  · exact row3680_10
  · exact row3680_11
theorem compare3680 (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps Program.sites n (configAt 3680 0 ⟨t,h,x,f⟩)
      (configAt 3680 12 ⟨if h=x then 0 else t,0,0,f⟩) :=
  compare bound3680 t h x f
#print axioms compare3680
end PA196.Source.AXGateCompare

