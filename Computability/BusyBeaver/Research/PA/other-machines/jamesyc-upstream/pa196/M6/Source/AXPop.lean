module
public import M6.Source.UnpairPartial
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXPop
open UnpairPartial
private theorem row_0 : resolveAt exactSites 77 = some (expected 77 0) := by rfl
private theorem row_1 : resolveAt exactSites 78 = some (expected 77 1) := by rfl
private theorem row_2 : resolveAt exactSites 79 = some (expected 77 2) := by rfl
private theorem row_3 : resolveAt exactSites 80 = some (expected 77 3) := by rfl
private theorem row_4 : resolveAt exactSites 81 = some (expected 77 4) := by rfl
private theorem row_5 : resolveAt exactSites 82 = some (expected 77 5) := by rfl
private theorem row_6 : resolveAt exactSites 83 = some (expected 77 6) := by rfl
private theorem row_7 : resolveAt exactSites 84 = some (expected 77 7) := by rfl
private theorem row_8 : resolveAt exactSites 85 = some (expected 77 8) := by rfl
private theorem row_9 : resolveAt exactSites 86 = some (expected 77 9) := by rfl
private theorem row_10 : resolveAt exactSites 87 = some (expected 77 10) := by rfl

theorem bound_first : Bound exactSites 77 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4
  · exact row_5
  · exact row_6
  · exact row_7
  · exact row_8
  · exact row_9
  · exact row_10

/-- The first actual AX formula-stack pop leaves the decoded head in X for
pairing, rather than falsely treating the continuation at88 as an exit. -/
theorem first_pop (n h : Nat) (f : Registers) :
    Steps exactSites (Unpair.loopCost n (0,0)+(3*(Cantor.decode n).2+1))
      (UnpairPartial.configAt 77 3933 ⟨n,h,0,0,f⟩)
      (UnpairPartial.configAt 77 3944 ⟨(Cantor.decode n).2,h,(Cantor.decode n).1,0,f⟩) :=
  decode_prefix bound_first n h f

#print axioms bound_first
#print axioms first_pop
end M6.Source.AXPop

