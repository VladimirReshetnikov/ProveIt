import PA194Words
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PA194AXOnce
open M6.Source.Cantor PA196.Commands PA196.Commands.Code PA194Words
attribute [local irreducible] PA194Words.run M6.Source.Cantor.pair PA194AXSymbolic.diagonal PA194AXReadable.guardedOldBundle

theorem ax_once (c w : Nat) :
    PA194Words.run [.ax c 0 0] ⟨0,w,0,0⟩ =
      some ⟨PA194AXReadable.guardedOldBundle 0 0 c,
        ([PA194AXSymbolic.diagonal c] ++ heads 0 0 c 0 0 ++ [0]).foldr pair w,0,0⟩ := by
  simp only [PA194Words.run, PA194Words.step, PA194CommandTransfer.step,Option.bind_some,Nat.zero_add]

#print axioms ax_once
end PA194AXOnce
