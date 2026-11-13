import DiophantineConsistency.Compact44.SelectedBandDecoder
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SelectedOrigin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits CompactPartialBand
open FixedGraphSelectedInputs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem origin_selected (n C : V) (T : ℕ) (ht : (T:V)<n)
    (h0 : dig 67 C 0=1) (hdecode : SelectedBandDecoder.Conclusion n C T) :
    CompactSelectorSum.Selected (selectorDigit n C (T:V) T) ⟨0, by decide⟩ ∧
      SelectedBandDecoder.copyWord n C T=Compact943Decoder.tileValue (V:=V) ⟨0, by decide⟩ := by
  have hone : selectorDigit n C (T:V) T ⟨0, by decide⟩ = 1 := by
    unfold selectorDigit
    simpa only [Nat.cast_zero] using (show dig 67 C (ArithmeticCyclicWord.cyc n (T:V) (((T-0):ℕ):V))=1 by
      rw [SelectedBandInputs.source_index n T 0 ht (Nat.zero_le T)]
      simpa only [Nat.cast_zero] using h0)
  rcases hdecode with hzero | ⟨i, hi, hword⟩
  · have hz := hzero.1 ⟨0, by decide⟩
    rw [hone] at hz
    exact False.elim (_root_.one_ne_zero hz)
  · have heq : i=⟨0, by decide⟩ := by
      by_contra hne
      have hz := hi.2 ⟨0, by decide⟩ (Ne.symm hne)
      rw [hone] at hz
      exact _root_.one_ne_zero hz
    subst i
    exact ⟨hi,hword⟩
#print axioms SelectedOrigin.origin_selected
end SelectedOrigin
