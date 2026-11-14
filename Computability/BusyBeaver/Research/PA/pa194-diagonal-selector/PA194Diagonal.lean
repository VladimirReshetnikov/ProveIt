import PA194Pops
import PA194ShiftTwo
import PA194AXOnce
import PA194HeadShape
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace PA194Diagonal
open M6.Source.Cantor PA196.Commands PA196.Commands.Code PA194Words PA194Selectors PA194ShiftTwo PA194AXOnce PA194HeadShape
attribute [local irreducible] PA194Words.pop PA194Words.discard PA194Words.run M6.Source.Cantor.pair PA194AXSymbolic.diagonal PA194AXReadable.guardedOldBundle

def selectDiagonal (c : Nat) : List Command :=
  discard ++ ([.ax c 0 0] ++ [.shift,.shift]) ++ pops 8

theorem selectDiagonal_total (c t w : Nat) :
    PA194Words.run (selectDiagonal c) ⟨t,w,0,0⟩ =
      some ⟨PA194AXSymbolic.diagonal c,w,0,0⟩ := by
  have hg : PA194AXReadable.guardedOldBundle 0 0 c ≠ 1 := by
    unfold PA194AXReadable.guardedOldBundle
    split
    · decide
    · simp [oldBundle,N]
  have hd : PA194AXSymbolic.diagonal c ≠ 1 := by
    unfold PA194AXSymbolic.diagonal
    exact I_ne_one _ _
  let rest := (PA194HeadShape.remaining 0 0 c 0 0 ++ [0]).foldr pair w
  have hax := ax_once c w
  rw [PA194HeadShape.shape] at hax
  have hs := shift_two (PA194AXReadable.guardedOldBundle 0 0 c) (PA194AXSymbolic.diagonal c)
    (head6 0 c 0) rest 0 hg hd
  have hp := pops_stack (PA194HeadShape.remaining 0 0 c 0 0) (PA194AXSymbolic.diagonal c) 0 w 0 (head6 0 c 0)
  have hh := append_total (append_total (append_total (discard_total t w) hax) hs) hp
  simpa only [selectDiagonal,PA194HeadShape.remaining_length,rest,Nat.reduceAdd,List.append_assoc] using hh

#print axioms selectDiagonal_total
end PA194Diagonal
