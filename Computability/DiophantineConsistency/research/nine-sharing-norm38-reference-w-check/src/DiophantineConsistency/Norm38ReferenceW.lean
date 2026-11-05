import DiophantineConsistency.Norm38ReferenceBase
import DiophantineConsistency.Carrier65

/-! One source-specific reference-field projection; no model bridge. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference

/-- Second reference field projection. -/
theorem reference_W {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 66 = (Carrier65.core p x).W := by
  simp [reference, Carrier65.core] <;> ring

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.reference_W
