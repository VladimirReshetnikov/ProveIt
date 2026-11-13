import DiophantineConsistency.Norm38ReferenceBase

/-! Proposed small DAG-edge cuts toward the U field identity. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference

theorem reference_78_edge {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 78 = reference p x 77 + reference p x 75 := by rfl

theorem reference_77_edge {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 77 = reference p x 73 * reference p x 76 := by rfl

theorem reference_76_edge {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 76 = reference p x 74 - reference p x 75 := by rfl

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.reference_78_edge
#print axioms DiophantineConsistency.Norm38Reference.reference_77_edge
#print axioms DiophantineConsistency.Norm38Reference.reference_76_edge
