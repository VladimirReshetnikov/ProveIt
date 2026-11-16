module
public import M6.Source.AXPair
public import M6.Source.AXTimes4
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXPairFirst
private theorem pair_0 : resolveAt exactSites 88 = some (AXPair.relocate 57 (AXPair.expected 6)) := by rfl
private theorem pair_1 : resolveAt exactSites 89 = some (AXPair.relocate 57 (AXPair.expected 7)) := by rfl
private theorem pair_2 : resolveAt exactSites 90 = some (AXPair.relocate 57 (AXPair.expected 8)) := by rfl
private theorem pair_3 : resolveAt exactSites 91 = some (AXPair.relocate 57 (AXPair.expected 9)) := by rfl
private theorem pair_4 : resolveAt exactSites 92 = some (AXPair.relocate 57 (AXPair.expected 10)) := by rfl
private theorem pair_5 : resolveAt exactSites 93 = some (AXPair.relocate 57 (AXPair.expected 11)) := by rfl
private theorem pair_6 : resolveAt exactSites 94 = some (AXPair.relocate 57 (AXPair.expected 12)) := by rfl
private theorem pair_7 : resolveAt exactSites 95 = some (AXPair.relocate 57 (AXPair.expected 13)) := by rfl
private theorem pair_8 : resolveAt exactSites 96 = some (AXPair.relocate 57 (AXPair.expected 14)) := by rfl
private theorem pair_9 : resolveAt exactSites 97 = some (AXPair.relocate 57 (AXPair.expected 15)) := by rfl
theorem pair_bound : AXPair.Bound exactSites 57 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_0
  · exact pair_1
  · exact pair_2
  · exact pair_3
  · exact pair_4
  · exact pair_5
  · exact pair_6
  · exact pair_7
  · exact pair_8
  · exact pair_9
private theorem times_0 : resolveAt exactSites 98 = some (AXTimes4.expected 98 0) := by rfl
private theorem times_1 : resolveAt exactSites 99 = some (AXTimes4.expected 98 1) := by rfl
private theorem times_2 : resolveAt exactSites 100 = some (AXTimes4.expected 98 2) := by rfl
private theorem times_3 : resolveAt exactSites 101 = some (AXTimes4.expected 98 3) := by rfl
private theorem times_4 : resolveAt exactSites 102 = some (AXTimes4.expected 98 4) := by rfl
private theorem times_5 : resolveAt exactSites 103 = some (AXTimes4.expected 98 5) := by rfl
theorem times_bound : AXTimes4.Bound exactSites 98 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact times_0
  · exact times_1
  · exact times_2
  · exact times_3
  · exact times_4
  · exact times_5
theorem pair_first (t w x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (AXPair.configAt 57 31 ⟨t,w,x,0,f⟩)
      (AXPair.configAt 57 41 ⟨0,w,0,Cantor.pair x t,f⟩) :=
  AXPair.pair pair_bound t w x f
theorem times4_first (t w x y : Nat) (f : Registers) :
    Steps exactSites (6*y+1) (AXTimes4.configAt 98 0 ⟨t,w,x,y,f⟩)
      (AXTimes4.configAt 98 6 ⟨t+4*y,w,x,0,f⟩) :=
  AXTimes4.times4 times_bound t w x y f
#print axioms pair_first
#print axioms times4_first
end M6.Source.AXPairFirst

