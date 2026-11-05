import DiophantineConsistency.Norm38ReferenceBase
import DiophantineConsistency.Carrier65

/-! Two source-specific reference-field projections; no model bridge. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference

/-- Reference node 61 is the first source norm. -/
theorem reference_P {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 61 = (Carrier65.core p x).P := by
  simp [reference, Carrier65.core] <;> ring

/-- Reference node 44 is the second source norm. -/
theorem reference_Q {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 44 = (Carrier65.core p x).Q := by
  simp [reference, Carrier65.core] <;> ring

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.reference_P
#print axioms DiophantineConsistency.Norm38Reference.reference_Q
