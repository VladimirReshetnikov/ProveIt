import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate21 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 21 = ringCompute GateOp.mul (reference p x 14) (reference p x 0) := by rfl

theorem reference_gate22 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 22 = ringCompute GateOp.add (reference p x 21) (reference p x 18) := by rfl

theorem reference_gate23 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 23 = ringCompute GateOp.mul (reference p x 22) (reference p x 22) := by rfl

theorem reference_gate24 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 24 = ringCompute GateOp.mul (reference p x 23) (reference p x 22) := by rfl

theorem reference_gate25 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 25 = ringCompute GateOp.mul (reference p x 8) (reference p x 22) := by rfl

end DiophantineConsistency.Norm38Reference
