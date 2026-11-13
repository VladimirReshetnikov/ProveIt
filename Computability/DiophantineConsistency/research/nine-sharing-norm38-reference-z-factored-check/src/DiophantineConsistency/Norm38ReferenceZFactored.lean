import DiophantineConsistency.Norm38ReferenceUFactored
import DiophantineConsistency.Norm38ReferenceDelta

/-! Proposed Z-field identity using checked S and delta projections. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference

theorem reference_Z_factored {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 80 = (Carrier65.core p x).Z := by
  have h80 : reference p x 80 = reference p x 79 - reference p x 73 := by rfl
  have h79 : reference p x 79 = reference p x 36 * reference p x 67 := by rfl
  have h67 : reference p x 67 = (Carrier65.core p x).f * (Carrier65.core p x).f := by rfl
  have h73 : reference p x 73 = reference p x 72 * reference p x 72 := by rfl
  have hZ : (Carrier65.core p x).Z =
      (Carrier65.core p x).delta * (Carrier65.core p x).f ^ 2 -
        (Carrier65.core p x).S ^ 2 := by rfl
  rw [h80, h79, reference_delta p x, h67, h73, reference_S_node p x, hZ]
  simp only [pow_two]

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.reference_Z_factored
