import DiophantineConsistency.Compact44.MarkerBlockIndex
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace MarkerSuccessor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactPartialBand CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem occupied_successor (N C h : V) (hN : 0<N) (hh : h<N)
    (heq : ∀ k<8807*N, k%8807=1073 →
      dig 67 C (cyc (8807*N) k 62)=dig 67 C (cyc (8807*N) k 8849))
    (hin : UniformBandInputs.Inputs (8807*N) C (8807*h+4393) 4393)
    (hsel : ∃ i : Fin 943, CompactSelectorSum.Selected (selectorDigit (8807*N) C (8807*h+4393) 4393) i ∧
      UniformBandDecoder.copyWord (8807*N) C (8807*h+4393) 4393=Compact943Decoder.tileValue (V:=V) i)
    (hdec : UniformBandDecoder.Conclusion (8807*N) C (8807*((h+1)%N)+4393) 4393) :
    ∃ i : Fin 943, CompactSelectorSum.Selected (selectorDigit (8807*N) C (8807*((h+1)%N)+4393) 4393) i ∧
      UniformBandDecoder.copyWord (8807*N) C (8807*((h+1)%N)+4393) 4393=Compact943Decoder.tileValue (V:=V) i := by
  let g := (h+1)%N
  have hg : g<N := mod_lt _ hN
  obtain ⟨i,hi,hw⟩ := hsel
  have hbit := DecodedOccupied.decoded_occupied (8807*N) C (8807*h+4393) 4393 i hin.2.1 hw ⟨34,by decide⟩ (by decide)
  unfold copyDigit at hbit
  have hidx := BlockSelectedMarker.copy_index N h 4393 ⟨34,by decide⟩ hh (by decide) (by decide)
  simp only [Nat.cast_ofNat] at hidx
  rw [hidx] at hbit
  have hmarker : dig 67 C (8807*h+1031)=1 := by simpa [position,slots] using hbit
  have he := MarkerBlockIndex.marker N C g hN hg heq
  rw [show cyc N g 1=h from BlockOrbit.forward_back N h 1 hN hh,hmarker] at he
  apply BlockSelectedMarker.selected_of_copy_one (8807*N) C (8807*g+4393) 4393 ⟨36,by decide⟩ _ hdec
  unfold copyDigit
  have hidx2 := BlockSelectedMarker.copy_index N g 4393 ⟨36,by decide⟩ hg (by decide) (by decide)
  simp only [Nat.cast_ofNat] at hidx2
  rw [hidx2]
  simpa [position,slots] using he
#print axioms MarkerSuccessor.occupied_successor
end MarkerSuccessor
