import DirectBFSSymbolicKernel
import DiophantineConsistency.Compact943Decoder

/-! Generic selector decoding for the direct-index BFS tile table. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSDecoder
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tileValue (i : Fin 943) : V :=
  CompactTilePayload.value ((DirectBFSSymbolicKernel.row i).1:V) ((DirectBFSSymbolicKernel.row i).2.1:V)
    ((DirectBFSSymbolicKernel.row i).2.2.1:V) ((DirectBFSSymbolicKernel.row i).2.2.2:V)

theorem tileValue_bounds (i : Fin 943) : 0<tileValue (V:=V) i ∧ tileValue (V:=V) i<Exp.exp 41 := by
  obtain ⟨hw,hn,he,hs⟩ := DirectBFSSymbolicKernel.row_bounds i
  have hw' : ((DirectBFSSymbolicKernel.row i).1:V)<256 := by exact_mod_cast hw
  have hn' : ((DirectBFSSymbolicKernel.row i).2.1:V)<512 := by exact_mod_cast hn
  have he' : ((DirectBFSSymbolicKernel.row i).2.2.1:V)<256 := by exact_mod_cast he
  have hs' : ((DirectBFSSymbolicKernel.row i).2.2.2:V)<512 := by exact_mod_cast hs
  exact CompactTilePayload.value_bounds _ _ _ _ hw' hn' he' hs'

theorem decode_iff (f : Fin 943 → V) (W : V) (hf : ∀ i,f i≤1) (hW : W<Exp.exp 41) :
    NoCarry ((∑ i,f i)+Exp.exp 10*((∑ i,(Exp.exp 41-tileValue (V:=V) i)*f i)+W)) (Exp.exp 51-2) ↔
    ((∀ i,f i=0) ∧ W=0) ∨ ∃ i,CompactSelectorSum.Selected f i ∧ W=tileValue (V:=V) i :=
  CompactDecoderIff.decode_iff f tileValue W (Compact943Decoder.count_bound f hf) hW tileValue_bounds

#print axioms DirectBFSDecoder.tileValue_bounds
#print axioms DirectBFSDecoder.decode_iff
end DirectBFSDecoder
