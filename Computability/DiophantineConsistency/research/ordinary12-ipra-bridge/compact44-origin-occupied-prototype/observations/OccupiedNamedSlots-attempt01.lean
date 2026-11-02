import DiophantineConsistency.FixedGraphSelectedOccupied
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace OccupiedNamedSlots
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits CompactSymbolicKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem named_slots (C : V) (h : FixedGraphSelectedOccupied.Occupied C) :
    dig 67 C 1095=1 ∧ dig 67 C 2195=1 ∧ dig 67 C 3296=1 := by
  have h₁ := h ⟨38, by decide⟩ (by decide)
  have h₂ := h ⟨39, by decide⟩ (by decide)
  have h₃ := h ⟨40, by decide⟩ (by decide)
  simpa only [position, slots, List.get_cons_zero, List.get_cons_succ] using And.intro h₁ (And.intro h₂ h₃)
#print axioms OccupiedNamedSlots.named_slots
end OccupiedNamedSlots
