import DiophantineConsistency.BFS943.DirectBFSWordLowFields
import DiophantineConsistency.Compact44.CompactWordPackingFields
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSConditionalPacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPacking
open DirectBFSConstructedWord CompactWordPackingFields
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pack_from_remaining_fields {row dummy : V → V} {d K HP N s : V}
    (hw : DirectBFSLocalWord.Word row N s) (h0 : dummy 0%2=0)
    (hN : 1<N) (hs : s<N)
    (hMC : (CompactConcreteIncrement.mask:V)+1<Exp.exp d)
    (hHPpos : 1≤HP) (hHPlt : HP<Exp.exp d)
    (hfields : TransportFields d K HP N s (cellWord row dummy)) :
    PackingInput d K CompactConcreteIncrement.mask HP N s (cellWord row dummy) := by
  obtain ⟨ho,hlo,hlow⟩ := DirectBFSWordLowFields.word_low_fields row dummy N s hw h0
  exact ⟨hN,hs,hfields.hi_lt,hMC,hHPpos,hHPlt,hfields.cell_sum,ho,
    hfields.blk_pos,hlo,fun j hj _ => hlow j hj,hfields.high_origin,hfields.high⟩
#print axioms DirectBFSConditionalPacking.pack_from_remaining_fields
end DirectBFSConditionalPacking
