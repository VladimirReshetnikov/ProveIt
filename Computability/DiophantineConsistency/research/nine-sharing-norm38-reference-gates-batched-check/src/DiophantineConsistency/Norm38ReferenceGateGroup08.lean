import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate61 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 61 = ringCompute GateOp.sub (reference p x 58) (reference p x 60) := by rfl

theorem reference_gate62 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 62 = ringCompute GateOp.add (reference p x 15) (reference p x 8) := by rfl

theorem reference_gate63 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 63 = ringCompute GateOp.mul (reference p x 62) (reference p x 46) := by rfl

theorem reference_gate64 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 64 = ringCompute GateOp.add (reference p x 63) (reference p x 45) := by rfl

theorem reference_gate65 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 65 = ringCompute GateOp.mul (reference p x 3) (reference p x 21) := by rfl

end DiophantineConsistency.Norm38Reference
