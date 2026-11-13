import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate41 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 41 = ringCompute GateOp.mul (reference p x 31) (reference p x 31) := by rfl

theorem reference_gate42 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 42 = ringCompute GateOp.mul (reference p x 36) (reference p x 41) := by rfl

theorem reference_gate43 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 43 = ringCompute GateOp.mul (reference p x 40) (reference p x 40) := by rfl

theorem reference_gate44 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 44 = ringCompute GateOp.sub (reference p x 43) (reference p x 42) := by rfl

theorem reference_gate45 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 45 = ringCompute GateOp.sub (reference p x 22) (reference p x 1) := by rfl

end DiophantineConsistency.Norm38Reference
