import DiophantineConsistency.Norm38ReferenceGateGroup00
import DiophantineConsistency.Norm38ReferenceGateGroup01
import DiophantineConsistency.Norm38ReferenceGateGroup02
import DiophantineConsistency.Norm38ReferenceGateGroup03
import DiophantineConsistency.Norm38ReferenceGateGroup04
import DiophantineConsistency.Norm38ReferenceGateGroup05
import DiophantineConsistency.Norm38ReferenceGateGroup06
import DiophantineConsistency.Norm38ReferenceGateGroup07
import DiophantineConsistency.Norm38ReferenceGateGroup08
import DiophantineConsistency.Norm38ReferenceGateGroup09
import DiophantineConsistency.Norm38ReferenceGateGroup10
import DiophantineConsistency.Norm38ReferenceGateGroup11

/-! Proposed gate-equation assembly; unchecked Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open SharingGateModel

theorem reference_gate_equations_batched {R : Type*} [CommRing R]
    (p : Fin 4 → R) (x : Fin 14 → R) :
    ∀ g ∈ NormAssignment38.gates,
      reference p x g.target = ringCompute g.op (reference p x g.left) (reference p x g.right) := by
  simp only [NormAssignment38.gates, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    false_implies, forall_const, and_true]
  exact ⟨reference_gate21 p x,
    reference_gate22 p x,
    reference_gate23 p x,
    reference_gate24 p x,
    reference_gate25 p x,
    reference_gate26 p x,
    reference_gate27 p x,
    reference_gate28 p x,
    reference_gate29 p x,
    reference_gate30 p x,
    reference_gate31 p x,
    reference_gate32 p x,
    reference_gate33 p x,
    reference_gate34 p x,
    reference_gate35 p x,
    reference_gate36 p x,
    reference_gate37 p x,
    reference_gate38 p x,
    reference_gate39 p x,
    reference_gate40 p x,
    reference_gate41 p x,
    reference_gate42 p x,
    reference_gate43 p x,
    reference_gate44 p x,
    reference_gate45 p x,
    reference_gate46 p x,
    reference_gate47 p x,
    reference_gate48 p x,
    reference_gate49 p x,
    reference_gate50 p x,
    reference_gate51 p x,
    reference_gate52 p x,
    reference_gate53 p x,
    reference_gate54 p x,
    reference_gate55 p x,
    reference_gate56 p x,
    reference_gate57 p x,
    reference_gate58 p x,
    reference_gate59 p x,
    reference_gate60 p x,
    reference_gate61 p x,
    reference_gate62 p x,
    reference_gate63 p x,
    reference_gate64 p x,
    reference_gate65 p x,
    reference_gate66 p x,
    reference_gate67 p x,
    reference_gate68 p x,
    reference_gate69 p x,
    reference_gate70 p x,
    reference_gate71 p x,
    reference_gate72 p x,
    reference_gate73 p x,
    reference_gate74 p x,
    reference_gate75 p x,
    reference_gate76 p x,
    reference_gate77 p x,
    reference_gate78 p x,
    reference_gate79 p x,
    reference_gate80 p x, by simp⟩

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.reference_gate_equations_batched
