import DiophantineConsistency.Compact44.OccupiedBits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SelectedOriginOccupied
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits CompactPartialBand CompactSymbolicKernel
open FixedGraphSelectedInputs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem selected_origin_occupied (n C : V) (T : ℕ) (ht : (T:V)<n) (hT : 3296≤T)
    (h0 : dig 67 C 0=1) (hin : Inputs n C T)
    (hdecode : SelectedBandDecoder.Conclusion n C T) :
    ∀ j : Fin 41, 34≤j.val → dig 67 C (position j:V)=1 := by
  have hw := (SelectedOrigin.origin_selected n C T ht h0 hdecode).2
  have hbig : (2181843386368:V) ≤ SelectedBandDecoder.copyWord n C T := by
    rw [hw]
    dsimp only [Compact943Decoder.tileValue, CompactTilePayload.value]
    have hpos : (0:V)≤((Compact943Data.row ⟨0, by decide⟩).1:V)+
      256*((Compact943Data.row ⟨0, by decide⟩).2.1:V)+
      131072*((Compact943Data.row ⟨0, by decide⟩).2.2.1:V)+
      33554432*((Compact943Data.row ⟨0, by decide⟩).2.2.2:V) := by simp
    have h := add_le_add hpos (le_refl (127*17179869184:V))
    norm_num only at h
    simpa only [zero_add, show (127:V)*17179869184=2181843386368 by norm_num] using h
  intro j hj
  have hbit : copyDigit position n C (T:V) T j=1 := by
    apply OccupiedBits.high_bits_one (copyDigit position n C (T:V) T) hin.2.1
    · exact hbig
    · exact hj
  have hall := ForeignBandGeometry.copy_allowed j
  unfold ForeignBandGeometry.Allowed at hall
  have hbound : position j≤3296 := by omega
  have hjT : position j≤T := le_trans hbound hT
  unfold copyDigit at hbit
  rw [SelectedBandInputs.source_index n T (position j) ht hjT] at hbit
  exact hbit
#print axioms SelectedOriginOccupied.selected_origin_occupied
end SelectedOriginOccupied
