import DiophantineConsistency.Norm38ReferenceFields01
import DiophantineConsistency.Norm38ReferenceW
import DiophantineConsistency.Norm38ReferenceDelta
import DiophantineConsistency.Norm38ReferenceUFactored
import DiophantineConsistency.Norm38ReferenceZFactored

/-! Proposed assembly of six checked reference-field projections. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference

theorem reference_terminal_fields_combined {R : Type*} [CommRing R]
    (p : Fin 4 → R) (x : Fin 14 → R) :
    let d := Carrier65.core p x
    reference p x 61 = d.P ∧ reference p x 44 = d.Q ∧
    reference p x 78 = d.U ∧ reference p x 66 = d.W ∧
    reference p x 80 = d.Z ∧ reference p x 36 = d.delta := by
  exact ⟨reference_P p x, reference_Q p x, reference_U_factored p x,
    reference_W p x, reference_Z_factored p x, reference_delta p x⟩

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.reference_terminal_fields_combined
