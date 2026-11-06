import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate71 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 71 = ringCompute GateOp.sub (reference p x 70) (reference p x 31) := by rfl

theorem reference_gate72 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 72 = ringCompute GateOp.mul (reference p x 5) (reference p x 42) := by rfl

theorem reference_gate73 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 73 = ringCompute GateOp.mul (reference p x 72) (reference p x 72) := by rfl

theorem reference_gate74 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 74 = ringCompute GateOp.mul (reference p x 71) (reference p x 71) := by rfl

theorem reference_gate75 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 75 = ringCompute GateOp.mul (reference p x 12) (reference p x 12) := by rfl

end DiophantineConsistency.Norm38Reference
