import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate76 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 76 = ringCompute GateOp.sub (reference p x 74) (reference p x 75) := by rfl

theorem reference_gate77 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 77 = ringCompute GateOp.mul (reference p x 73) (reference p x 76) := by rfl

theorem reference_gate78 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 78 = ringCompute GateOp.add (reference p x 77) (reference p x 75) := by rfl

theorem reference_gate79 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 79 = ringCompute GateOp.mul (reference p x 36) (reference p x 67) := by rfl

theorem reference_gate80 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 80 = ringCompute GateOp.sub (reference p x 79) (reference p x 73) := by rfl

end DiophantineConsistency.Norm38Reference
