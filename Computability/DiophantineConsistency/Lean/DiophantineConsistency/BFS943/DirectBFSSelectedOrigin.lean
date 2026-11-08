import DiophantineConsistency.BFS943.DirectBFSRawColumn
import DiophantineConsistency.Compact44.SelectedOriginOccupied

/-! Direct-BFS selected row and occupied origin, with no graph premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSSelectedOrigin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticBinaryCarry ArithmeticWindowDigits CompactPartialBand CompactSymbolicKernel
open FixedGraphSelectedInputs
attribute [local irreducible] DirectBFSSymbolicKernel.rows Compact943Data.rows
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def copyWord (n C : V) (T : ℕ) : V :=
  ∑ j : Fin 41,(2:V)^j.val*copyDigit position n C (T:V) T j

def decoderBand (n C : V) (T : ℕ) : V :=
  (∑ j,selectorDigit n C (T:V) T j)+Exp.exp 10*
    ((∑ j,(Exp.exp 41-DirectBFSDecoder.tileValue (V:=V) j)*selectorDigit n C (T:V) T j)+copyWord n C T)

def Conclusion (n C : V) (T : ℕ) : Prop :=
  ((∀ j : Fin 943,selectorDigit n C (T:V) T j=0) ∧ copyWord n C T=0) ∨
  ∃ j : Fin 943,CompactSelectorSum.Selected (selectorDigit n C (T:V) T) j ∧
    copyWord n C T=DirectBFSDecoder.tileValue (V:=V) j

theorem decode (n C : V) (T : ℕ) (hin : Inputs n C T)
    (hnc : NoCarry (decoderBand n C T) (Exp.exp 51-2)) : Conclusion n C T := by
  obtain ⟨hs,_hc,hw⟩ := hin
  have hdecode := DirectBFSDecoder.decode_iff (selectorDigit n C (T:V) T) (copyWord n C T) hs hw
  exact hdecode.mp hnc

theorem first_tile_equal : DirectBFSDecoder.tileValue (V:=V) ⟨0,by decide⟩ =
    Compact943Decoder.tileValue (V:=V) ⟨0,by decide⟩ := by
  unfold DirectBFSDecoder.tileValue Compact943Decoder.tileValue
  unfold DirectBFSSymbolicKernel.row Compact943Data.row DirectBFSSymbolicKernel.rows Compact943Data.rows
  rfl

theorem to_original_conclusion_at_origin (n C : V) (T : ℕ) (ht : (T:V)<n)
    (h0 : dig 67 C 0=1) (hdecode : Conclusion n C T) :
    SelectedBandDecoder.Conclusion n C T := by
  have hone : selectorDigit n C (T:V) T ⟨0,by decide⟩=1 := by
    unfold selectorDigit
    simpa only [Nat.cast_zero] using (show dig 67 C (ArithmeticCyclicWord.cyc n (T:V) (((T-0):ℕ):V))=1 by
      rw [SelectedBandInputs.source_index n T 0 ht (Nat.zero_le T)]
      simpa only [Nat.cast_zero] using h0)
  rcases hdecode with hzero | ⟨i,hi,hword⟩
  · exact Or.inl hzero
  · have heq : i=⟨0,by decide⟩ := by
      by_contra hne
      have hz := hi.2 ⟨0,by decide⟩ (Ne.symm hne)
      rw [hone] at hz
      exact _root_.one_ne_zero hz
    subst i
    apply Or.inr
    refine ⟨⟨0,by decide⟩,hi,?_⟩
    change copyWord n C T=Compact943Decoder.tileValue (V:=V) ⟨0,by decide⟩
    rw [←first_tile_equal]
    exact hword

theorem selected_origin_occupied (n C : V) (T : ℕ) (ht : (T:V)<n) (hT : 3296≤T)
    (h0 : dig 67 C 0=1) (hin : Inputs n C T) (hdecode : Conclusion n C T) :
    ∀ j : Fin 41,34≤j.val → dig 67 C (position j:V)=1 :=
  SelectedOriginOccupied.selected_origin_occupied n C T ht hT h0 hin
    (to_original_conclusion_at_origin n C T ht h0 hdecode)

#print axioms DirectBFSSelectedOrigin.decode
#print axioms DirectBFSSelectedOrigin.first_tile_equal
#print axioms DirectBFSSelectedOrigin.selected_origin_occupied
end DirectBFSSelectedOrigin
