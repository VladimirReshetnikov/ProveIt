import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate26 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 26 = ringCompute GateOp.mul (reference p x 7) (reference p x 24) := by rfl

theorem reference_gate27 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 27 = ringCompute GateOp.mul (reference p x 25) (reference p x 26) := by rfl

theorem reference_gate28 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 28 = ringCompute GateOp.add (reference p x 10) (reference p x 11) := by rfl

theorem reference_gate29 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 29 = ringCompute GateOp.mul (reference p x 28) (reference p x 26) := by rfl

theorem reference_gate30 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 30 = ringCompute GateOp.mul (reference p x 27) (reference p x 29) := by rfl

end DiophantineConsistency.Norm38Reference
