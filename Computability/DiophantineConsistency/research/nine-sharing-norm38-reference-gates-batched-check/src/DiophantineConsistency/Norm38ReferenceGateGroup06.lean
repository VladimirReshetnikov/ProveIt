import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate51 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 51 = ringCompute GateOp.mul (reference p x 22) (reference p x 17) := by rfl

theorem reference_gate52 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 52 = ringCompute GateOp.add (reference p x 16) (reference p x 51) := by rfl

theorem reference_gate53 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 53 = ringCompute GateOp.mul (reference p x 52) (reference p x 0) := by rfl

theorem reference_gate54 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 54 = ringCompute GateOp.add (reference p x 50) (reference p x 53) := by rfl

theorem reference_gate55 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 55 = ringCompute GateOp.mul (reference p x 27) (reference p x 9) := by rfl

end DiophantineConsistency.Norm38Reference
