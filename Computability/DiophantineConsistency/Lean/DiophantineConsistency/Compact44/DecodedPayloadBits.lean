import DiophantineConsistency.Compact44.BinarySliceEqual
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DecodedPayloadBits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits CompactPartialBand CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bit (N C h : V) (i : Fin 943) (j : Fin 41) (hh : h<N)
    (hin : UniformBandInputs.Inputs (8807*N) C (8807*h+4393) 4393)
    (hw : UniformBandDecoder.copyWord (8807*N) C (8807*h+4393) 4393=Compact943Decoder.tileValue (V:=V) i) :
    dig 67 C (8807*h+(position j:V))=fbit (Compact943Decoder.tileValue (V:=V) i) (j.val:V) := by
  have hb := FiniteBinaryWord.bit 41 (copyDigit position (8807*N) C (8807*h+4393) 4393) hin.2.1 j
  change fbit (UniformBandDecoder.copyWord (8807*N) C (8807*h+4393) 4393) (j.val:V) = _ at hb
  rw [hw] at hb
  unfold copyDigit at hb
  have hj : position j≤4393 := by
    have ha := ForeignBandGeometry.copy_allowed j
    unfold ForeignBandGeometry.Allowed at ha
    omega
  have hi := BlockSelectedMarker.copy_index N h 4393 j hh (by decide) hj
  simp only [Nat.cast_ofNat] at hi
  rw [hi] at hb
  exact hb.symm
#print axioms DecodedPayloadBits.bit
end DecodedPayloadBits
