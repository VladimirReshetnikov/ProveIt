import DiophantineConsistency.BFS943.DirectBFSConditionalPacking
import DiophantineConsistency.BFS943.DirectBFSCellProduct
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSFourFieldsPacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPacking ArithmeticBinaryCarry
open DirectBFSConstructedWord CompactWordPackingFields
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def kernel : V := ((DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho:ℕ):V)

structure RemainingFields (HP N s : V) (X : V → V) : Prop where
  cell_sum : ∀ j<N, X j+blk 590069 kernel N s X j<Exp.exp 590069
  blk_pos : 0<blk 590069 kernel N s X 0
  high_origin : NoCarry (blk 590069 kernel N s X 0) (HP-1)
  high : ∀ j<N, 0<j → NoCarry (blk 590069 kernel N s X j) HP

theorem pack_from_four_fields {row dummy : V → V} {HP N s : V}
    (hw : DirectBFSLocalWord.Word row N s) (h0 : dummy 0%2=0)
    (hN : 1<N) (hs : s<N)
    (hMC : (CompactConcreteIncrement.mask:V)+1<Exp.exp 590069)
    (hHPpos : 1≤HP) (hHPlt : HP<Exp.exp 590069)
    (hfields : RemainingFields HP N s (cellWord row dummy)) :
    PackingInput 590069 kernel CompactConcreteIncrement.mask HP N s (cellWord row dummy) := by
  apply DirectBFSConditionalPacking.pack_from_remaining_fields hw h0 hN hs hMC hHPpos hHPlt
  refine ⟨?_,hfields.cell_sum,hfields.blk_pos,hfields.high_origin,hfields.high⟩
  intro j hj
  exact DirectBFSCellProduct.normalized_cell_product_lt (row j) (dummy j) (hw.tile_ne j hj)
#print axioms DirectBFSFourFieldsPacking.pack_from_four_fields
end DirectBFSFourFieldsPacking
