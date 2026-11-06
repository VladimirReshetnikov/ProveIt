import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate31 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 31 = ringCompute GateOp.add (reference p x 29) (reference p x 10) := by rfl

theorem reference_gate32 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 32 = ringCompute GateOp.add (reference p x 27) (reference p x 26) := by rfl

theorem reference_gate33 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 33 = ringCompute GateOp.mul (reference p x 20) (reference p x 32) := by rfl

theorem reference_gate34 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 34 = ringCompute GateOp.add (reference p x 33) (reference p x 19) := by rfl

theorem reference_gate35 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 35 = ringCompute GateOp.mul (reference p x 32) (reference p x 32) := by rfl

end DiophantineConsistency.Norm38Reference
