import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate66 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 66 = ringCompute GateOp.sub (reference p x 64) (reference p x 65) := by rfl

theorem reference_gate67 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 67 = ringCompute GateOp.mul (reference p x 4) (reference p x 4) := by rfl

theorem reference_gate68 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 68 = ringCompute GateOp.mul (reference p x 31) (reference p x 6) := by rfl

theorem reference_gate69 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 69 = ringCompute GateOp.sub (reference p x 68) (reference p x 54) := by rfl

theorem reference_gate70 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 70 = ringCompute GateOp.mul (reference p x 67) (reference p x 69) := by rfl

end DiophantineConsistency.Norm38Reference
