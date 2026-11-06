import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate56 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 56 = ringCompute GateOp.add (reference p x 55) (reference p x 28) := by rfl

theorem reference_gate57 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 57 = ringCompute GateOp.sub (reference p x 56) (reference p x 54) := by rfl

theorem reference_gate58 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 58 = ringCompute GateOp.mul (reference p x 57) (reference p x 57) := by rfl

theorem reference_gate59 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 59 = ringCompute GateOp.add (reference p x 30) (reference p x 28) := by rfl

theorem reference_gate60 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 60 = ringCompute GateOp.mul (reference p x 30) (reference p x 59) := by rfl

end DiophantineConsistency.Norm38Reference
