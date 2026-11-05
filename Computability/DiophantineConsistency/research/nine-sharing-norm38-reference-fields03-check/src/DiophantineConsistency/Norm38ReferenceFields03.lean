import DiophantineConsistency.Norm38ReferenceBase
import DiophantineConsistency.Carrier65

/-! Two source-specific reference-field projections; no model bridge. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference

/-- First reference field projection. -/
theorem reference_Z {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 80 = (Carrier65.core p x).Z := by
  simp [reference, Carrier65.core] <;> ring

/-- Second reference field projection. -/
theorem reference_delta {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 36 = (Carrier65.core p x).delta := by
  simp [reference, Carrier65.core] <;> ring

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.reference_Z
#print axioms DiophantineConsistency.Norm38Reference.reference_delta
