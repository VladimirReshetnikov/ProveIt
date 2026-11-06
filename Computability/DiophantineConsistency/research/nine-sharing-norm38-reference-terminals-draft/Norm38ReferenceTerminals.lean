import DiophantineConsistency.Norm38ReferenceInitial
import DiophantineConsistency.Norm38ReferenceGatesAll

/-! Uncompiled draft: terminal agreement from initial agreement and all gate equations. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Static gate constraints identify the six named terminals with the source
reference, assuming the separately checked graph and initial agreement. -/
theorem static_terminals_agree (ports : Fin 4 → V) (w : Fin 38 → V)
    (hg : NormAssignment38.gatesHold ι ports w) :
    let v := NormAssignment38.assignment ports w
    let ref := reference (fun j => ι (ports j))
      (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
    pairValue ι (v 61)=ref 61 ∧ pairValue ι (v 44)=ref 44 ∧
    pairValue ι (v 78)=ref 78 ∧ pairValue ι (v 66)=ref 66 ∧
    pairValue ι (v 80)=ref 80 ∧ pairValue ι (v 36)=ref 36 := by
  let val := fun j => pairValue ι (NormAssignment38.assignment ports w j)
  let ref := reference (fun j => ι (ports j))
    (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
  have hfixed : val = ringRun NormAssignment38.gates val :=
    SharingTopology38.static_assignment_fixed ι ports w hg
  have hrun := SharingTopology38.ringRun_agrees_of_topological
    NormAssignment38.gates initialNodes val ref graph_topological
    (initial_agreement ports w) (reference_gate_equations_batched _ _)
  have heq (i : Fin 81) (hi : i ∈ completed NormAssignment38.gates initialNodes) :
      val i = ref i := (congrFun hfixed i).trans (hrun i hi)
  exact ⟨heq 61 (by decide), heq 44 (by decide), heq 78 (by decide),
    heq 66 (by decide), heq 80 (by decide), heq 36 (by decide)⟩
end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.static_terminals_agree
