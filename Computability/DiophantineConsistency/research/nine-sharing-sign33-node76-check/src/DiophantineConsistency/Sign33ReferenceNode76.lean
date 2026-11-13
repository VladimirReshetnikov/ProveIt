import DiophantineConsistency.Norm38ReferenceFieldsAll

/-! The reference node 76 is V²-y², over an arbitrary commutative ring. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ReferenceNode76
open Norm38Reference

theorem reference76 {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 76 = (Carrier65.core p x).V * (Carrier65.core p x).V -
      (Carrier65.core p x).y * (Carrier65.core p x).y := by
  have h74 : reference p x 74 = reference p x 71 * reference p x 71 := by rfl
  have h75 : reference p x 75 = (Carrier65.core p x).y * (Carrier65.core p x).y := by rfl
  rw [reference_76_edge, h74, h75, reference_V_node]
end DiophantineConsistency.Sign33ReferenceNode76
#print axioms DiophantineConsistency.Sign33ReferenceNode76.reference76
