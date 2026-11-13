import DiophantineConsistency.Norm38ReferenceTerminals

/-! A single additional static node follows from the checked topology. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33StaticNode76
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem node76 (ports : Fin 4 → V) (w : Fin 38 → V)
    (hg : NormAssignment38.gatesHold ι ports w) :
    pairValue ι (NormAssignment38.assignment ports w 76) =
      Norm38Reference.reference (fun j => ι (ports j))
        (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j)+1)) 76 := by
  let val := fun j => pairValue ι (NormAssignment38.assignment ports w j)
  let ref := Norm38Reference.reference (fun j => ι (ports j))
    (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j)+1))
  have hfixed : val = ringRun NormAssignment38.gates val :=
    SharingTopology38.static_assignment_fixed ι ports w hg
  have hrun := SharingTopology38.ringRun_agrees_of_topological
    NormAssignment38.gates Norm38Reference.initialNodes val ref Norm38Reference.graph_topological
    (Norm38Reference.initial_agreement ports w) (Norm38Reference.reference_gate_equations_batched _ _)
  exact (congrFun hfixed 76).trans (hrun 76 (by decide))
end DiophantineConsistency.Sign33StaticNode76
#print axioms DiophantineConsistency.Sign33StaticNode76.node76
