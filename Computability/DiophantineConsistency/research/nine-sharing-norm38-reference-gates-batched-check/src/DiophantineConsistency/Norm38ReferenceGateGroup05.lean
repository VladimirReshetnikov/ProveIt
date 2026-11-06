import DiophantineConsistency.Norm38ReferenceBase

/-! Source-only proposed bounded reference-gate group; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate46 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 46 = ringCompute GateOp.sub (reference p x 45) (reference p x 2) := by rfl

theorem reference_gate47 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 47 = ringCompute GateOp.mul (reference p x 21) (reference p x 45) := by rfl

theorem reference_gate48 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 48 = ringCompute GateOp.add (reference p x 47) (reference p x 2) := by rfl

theorem reference_gate49 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 49 = ringCompute GateOp.sub (reference p x 23) (reference p x 18) := by rfl

theorem reference_gate50 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 50 = ringCompute GateOp.mul (reference p x 48) (reference p x 49) := by rfl

end DiophantineConsistency.Norm38Reference
