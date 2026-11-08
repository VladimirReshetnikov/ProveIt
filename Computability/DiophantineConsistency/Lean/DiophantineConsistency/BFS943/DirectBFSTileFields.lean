import DiophantineConsistency.BFS943.DirectBFSDecoder
import DiophantineConsistency.Compact44.TilePayloadFields

/-! Recover typed edge labels from direct-BFS tile payload bits. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSTileFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticStandardCasts TilePayloadFields
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem tile_fields (i : Fin 943) :
    BinarySliceEqual.slice (DirectBFSDecoder.tileValue (V:=V) i) 25 9=((DirectBFSSymbolicKernel.row i).2.2.2:V) ∧
    BinarySliceEqual.slice (DirectBFSDecoder.tileValue (V:=V) i) 8 9=((DirectBFSSymbolicKernel.row i).2.1:V) ∧
    BinarySliceEqual.slice (DirectBFSDecoder.tileValue (V:=V) i) 17 8=((DirectBFSSymbolicKernel.row i).2.2.1:V) ∧
    BinarySliceEqual.slice (DirectBFSDecoder.tileValue (V:=V) i) 0 8=((DirectBFSSymbolicKernel.row i).1:V) := by
  let r := DirectBFSSymbolicKernel.row i
  have hval : DirectBFSDecoder.tileValue (V:=V) i=(val r.1 r.2.1 r.2.2.1 r.2.2.2:V) := by
    simp only [DirectBFSDecoder.tileValue,CompactTilePayload.value,val,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,r]
  obtain ⟨hw,hn,he,hs⟩ := DirectBFSSymbolicKernel.row_bounds i
  have hnats := natural_fields r.1 r.2.1 r.2.2.1 r.2.2.2 hw hn he hs
  rw [hval]
  have hsouth := slice_cast (V:=V) (val r.1 r.2.1 r.2.2.1 r.2.2.2) 25 9
  have hnorth := slice_cast (V:=V) (val r.1 r.2.1 r.2.2.1 r.2.2.2) 8 9
  have heast := slice_cast (V:=V) (val r.1 r.2.1 r.2.2.1 r.2.2.2) 17 8
  have hwest := slice_cast (V:=V) (val r.1 r.2.1 r.2.2.1 r.2.2.2) 0 8
  simp only [Nat.cast_ofNat,hnats.1] at hsouth
  simp only [Nat.cast_ofNat,hnats.2.1] at hnorth
  simp only [Nat.cast_ofNat,hnats.2.2.1] at heast
  simp only [Nat.cast_ofNat,hnats.2.2.2] at hwest
  exact ⟨hsouth,hnorth,heast,hwest⟩

#print axioms DirectBFSTileFields.tile_fields
end DirectBFSTileFields
