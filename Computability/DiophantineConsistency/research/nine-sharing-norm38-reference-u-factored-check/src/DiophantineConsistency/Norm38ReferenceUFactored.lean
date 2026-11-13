import DiophantineConsistency.Norm38ReferenceUEdges
import DiophantineConsistency.Carrier65

/-! Proposed U-field identity using checked shared reference DAG edges. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference

theorem reference_V_node {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 71 = (Carrier65.core p x).V := by
  simp [reference, Carrier65.core] <;> ring

theorem reference_S_node {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 72 = (Carrier65.core p x).S := by
  simp [reference, Carrier65.core] <;> ring

theorem reference_U_factored {R : Type*} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :
    reference p x 78 = (Carrier65.core p x).U := by
  have h73 : reference p x 73 = reference p x 72 * reference p x 72 := by rfl
  have h74 : reference p x 74 = reference p x 71 * reference p x 71 := by rfl
  have h75 : reference p x 75 = (Carrier65.core p x).y * (Carrier65.core p x).y := by rfl
  have hU : (Carrier65.core p x).U =
      (Carrier65.core p x).S ^ 2 * ((Carrier65.core p x).V ^ 2 - (Carrier65.core p x).y ^ 2) +
        (Carrier65.core p x).y ^ 2 := by rfl
  rw [reference_78_edge, reference_77_edge, reference_76_edge, h73, h74, h75,
    reference_S_node p x, reference_V_node p x, hU]
  simp only [pow_two]

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.reference_V_node
#print axioms DiophantineConsistency.Norm38Reference.reference_S_node
#print axioms DiophantineConsistency.Norm38Reference.reference_U_factored
