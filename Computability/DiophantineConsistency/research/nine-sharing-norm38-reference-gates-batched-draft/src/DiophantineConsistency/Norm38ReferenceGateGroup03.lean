import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate36 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 36 = ringCompute GateOp.add (reference p x 35) (reference p x 34) := by rfl

theorem reference_gate37 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 37 = ringCompute GateOp.mul (reference p x 32) (reference p x 31) := by rfl

theorem reference_gate38 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 38 = ringCompute GateOp.add (reference p x 25) (reference p x 37) := by rfl

theorem reference_gate39 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 39 = ringCompute GateOp.mul (reference p x 13) (reference p x 34) := by rfl

theorem reference_gate40 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 40 = ringCompute GateOp.add (reference p x 38) (reference p x 39) := by rfl

end DiophantineConsistency.Norm38Reference
