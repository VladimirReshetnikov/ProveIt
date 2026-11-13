import DiophantineConsistency.SelectedBandInputs
import DiophantineConsistency.CompactCopyBound
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SelectedBandWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open CompactSymbolicKernel CompactPartialBand
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bounded (n C : V) (T : ℕ) (ht : (T:V)<n) (hT : 3296≤T)
    (hbool : ∀ k<n, k%8807≠1063 → DiophantineConsistency.ArithmeticWindowDigits.dig 67 C k≤1) :
    (∀ j : Fin 943, selectorDigit n C (T:V) T j≤1) ∧
    (∀ j : Fin 41, copyDigit position n C (T:V) T j≤1) ∧
    (∑ j : Fin 41, (2:V)^j.val*copyDigit position n C (T:V) T j)<Exp.exp 41 := by
  obtain ⟨hs,hc⟩ := SelectedBandInputs.selected_inputs n C T ht hT hbool
  exact ⟨hs,hc,CompactCopyBound.copy_bound _ hc⟩
#print axioms SelectedBandWord.bounded
end SelectedBandWord
