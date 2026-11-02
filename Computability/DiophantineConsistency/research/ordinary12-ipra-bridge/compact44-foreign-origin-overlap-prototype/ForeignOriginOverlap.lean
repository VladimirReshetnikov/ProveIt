import DiophantineConsistency.DecodedSelectorShift
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ForeignOriginOverlap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactPartialBand
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem selector_origin (n C : V) (T : ℕ) (i : Fin 943)
    (hoff : (((T-i.val):ℕ):V)<n) (h0 : dig 67 C 0=1) :
    selectorDigit n C (((T-i.val):ℕ):V) T i=1 := by
  unfold selectorDigit
  rw [cyc_of_le hoff hoff le_rfl, tsub_self]
  exact h0

theorem overlap_5488 (n C : V) (hn : (5488:V)<n) (h0 : dig 67 C 0=1) :
    selectorDigit n C 5488 5495 ⟨7, by decide⟩=1 := by
  simpa only [show 5495-7=5488 by decide, Nat.cast_ofNat] using
    selector_origin n C 5495 ⟨7, by decide⟩ hn h0
#print axioms ForeignOriginOverlap.selector_origin
#print axioms ForeignOriginOverlap.overlap_5488
end ForeignOriginOverlap
