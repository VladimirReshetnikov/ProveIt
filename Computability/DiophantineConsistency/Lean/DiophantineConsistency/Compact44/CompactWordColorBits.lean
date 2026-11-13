import DiophantineConsistency.Compact44.CompactWordCellClient
import DiophantineConsistency.Compact44.TilePayloadFields

/-! Forward bitwise consequences of a compact word's tile-color matching. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordColorBits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits
open CompactRowTransport CompactMarkedTransport CompactWordCellClient CompactForwardCellInputs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Vertical neighbor matching equates each south bit of one row with the
corresponding north bit of its cyclic predecessor. -/
theorem vertical_bits {row : V → V} {N s j j' : V}
    (hw : CompactWord row N s) (hj : j<N) (hj' : j'<N) (he : (j'+s)%N=j)
    (u : V) (hu : u<9) :
    fbit (payload (row j)) (25+u) = fbit (payload (row j')) (8+u) := by
  obtain ⟨i, hi⟩ := standard_row (hw.tile_lt j hj)
  obtain ⟨i', hi'⟩ := standard_row (hw.tile_lt j' hj')
  have hc := hw.south j hj j' hj' he
  rw [hi, hi', field_row (fun t => t.2.2.2) rfl i,
    field_row (fun t => t.2.1) rfl i'] at hc
  have hb := congrArg (fun x : V => fbit x u) hc
  rw [hi, hi', payload_row i, payload_row i']
  have hs := BinarySliceEqual.bit_slice (Compact943Decoder.tileValue (V:=V) i) 25 9 u hu
  have hn := BinarySliceEqual.bit_slice (Compact943Decoder.tileValue (V:=V) i') 8 9 u hu
  rw [(TilePayloadFields.tile_fields i).1] at hs
  rw [(TilePayloadFields.tile_fields i').2.1] at hn
  exact hs.symm.trans (hb.trans hn)

/-- Horizontal neighbor matching equates each east bit of one row with the
corresponding west bit of its cyclic predecessor. -/
theorem horizontal_bits {row : V → V} {N s j j' : V}
    (hw : CompactWord row N s) (hj : j<N) (hj' : j'<N) (he : (j'+1)%N=j)
    (u : V) (hu : u<8) :
    fbit (payload (row j)) (17+u) = fbit (payload (row j')) u := by
  obtain ⟨i, hi⟩ := standard_row (hw.tile_lt j hj)
  obtain ⟨i', hi'⟩ := standard_row (hw.tile_lt j' hj')
  have hc := hw.east j hj j' hj' he
  rw [hi, hi', field_row (fun t => t.2.2.1) rfl i,
    field_row (fun t => t.1) rfl i'] at hc
  have hb := congrArg (fun x : V => fbit x u) hc
  rw [hi, hi', payload_row i, payload_row i']
  have hs := BinarySliceEqual.bit_slice (Compact943Decoder.tileValue (V:=V) i) 17 8 u hu
  have hn := BinarySliceEqual.bit_slice (Compact943Decoder.tileValue (V:=V) i') 0 8 u hu
  rw [(TilePayloadFields.tile_fields i).2.2.1] at hs
  rw [(TilePayloadFields.tile_fields i').2.2.2] at hn
  simpa using hs.symm.trans (hb.trans hn)

#print axioms CompactWordColorBits.vertical_bits
#print axioms CompactWordColorBits.horizontal_bits
end CompactWordColorBits
