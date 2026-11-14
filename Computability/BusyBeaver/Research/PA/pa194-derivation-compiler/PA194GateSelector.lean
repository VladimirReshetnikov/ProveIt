import PA194Pops
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace PA194GateSelector
open M6.Source.Cantor PA196.Commands PA196.Commands.Code PA194Words PA194Selectors
attribute [local irreducible] PA194Words.pop PA194Words.discard PA194Words.run M6.Source.Cantor.pair PA194AXSymbolic.diagonal PA194AXReadable.guardedOldBundle

def headStack (D H A d h : Nat) : List Nat := [PA194AXSymbolic.diagonal A] ++ heads D H A d h
@[simp] theorem headStack_length (D H A d h : Nat) : (headStack D H A d h).length = 9 := rfl

def selectGate (a b c : Nat) : List Command := discard ++ [.ax c b a] ++ pops 10

theorem selectGate_total (a b c t w : Nat) :
    PA194Words.run (selectGate a b c) ⟨t,w,0,0⟩ =
      some ⟨PA194AXReadable.guardedOldBundle a b c,w,0,0⟩ := by
  have hx : PA194Words.run [.ax c b a] ⟨0,w,0,0⟩ =
      some ⟨PA194AXReadable.guardedOldBundle a b c,(headStack b a c 0 0 ++ [0]).foldr pair w,0,0⟩ := by
    simp only [PA194Words.run, PA194Words.step, PA194CommandTransfer.step,Option.bind_some,
      Nat.zero_add,headStack]
  have hp := pops_stack (headStack b a c 0 0) (PA194AXReadable.guardedOldBundle a b c) 0 w 0 0
  have hr := append_total (append_total (discard_total t w) hx) hp
  simpa only [selectGate,headStack_length,Nat.reduceAdd,List.append_assoc] using hr

#print axioms selectGate_total
end PA194GateSelector
