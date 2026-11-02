import DiophantineConsistency.OccupiedBits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DecodedOccupied
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits CompactPartialBand CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem decoded_occupied (n C k : V) (T : ℕ) (i : Fin 943)
    (hb : ∀ j, copyDigit position n C k T j≤1)
    (hw : (∑ j : Fin 41, (2:V)^j.val*copyDigit position n C k T j)=Compact943Decoder.tileValue (V:=V) i) :
    ∀ j : Fin 41, 34≤j.val → copyDigit position n C k T j=1 := by
  have hbig : (2181843386368:V) ≤ ∑ j : Fin 41, (2:V)^j.val*copyDigit position n C k T j := by
    rw [hw]
    dsimp only [Compact943Decoder.tileValue, CompactTilePayload.value]
    have hpos : (0:V)≤((Compact943Data.row i).1:V)+
      256*((Compact943Data.row i).2.1:V)+
      131072*((Compact943Data.row i).2.2.1:V)+
      33554432*((Compact943Data.row i).2.2.2:V) := by simp
    have h := add_le_add hpos (le_refl (127*17179869184:V))
    norm_num only at h
    simpa only [zero_add, show (127:V)*17179869184=2181843386368 by norm_num] using h
  intro j hj
  exact OccupiedBits.high_bits_one _ hb hbig j hj
#print axioms DecodedOccupied.decoded_occupied
end DecodedOccupied
