import DiophantineConsistency.Sign33RingTopology
import DiophantineConsistency.Sign33RingGatesAssembly
import DiophantineConsistency.Norm38ReferenceTerminals

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33LiftTerminals
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem terminals (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let a := NormAssignment38.assignment ports (Sign33Lift38.lift v)
    let ref := Norm38Reference.reference (fun j => ι (ports j))
      (fun j => ι (Sign33Lift38.lift v (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
    pairValue ι (a 61)=ref 61 ∧ pairValue ι (a 44)=ref 44 ∧
    pairValue ι (a 78)=ref 78 ∧ pairValue ι (a 66)=ref 66 ∧
    pairValue ι (a 80)=ref 80 ∧ pairValue ι (a 36)=ref 36 := by
  let val := fun j => pairValue ι (NormAssignment38.assignment ports (Sign33Lift38.lift v) j)
  let ref := Norm38Reference.reference (fun j => ι (ports j))
    (fun j => ι (Sign33Lift38.lift v (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
  have hrun := Sign33RingTopology.static_agrees_of_topological
    NormAssignment38.gates Norm38Reference.initialNodes val ref Norm38Reference.graph_topological
    (Norm38Reference.initial_agreement ports (Sign33Lift38.lift v))
    (Norm38Reference.reference_gate_equations_batched _ _)
    (Sign33RingGatesAssembly.all_ring_gates ports v hc)
  have heq (i : Fin 81) (hi : i ∈ completed NormAssignment38.gates Norm38Reference.initialNodes) :
      val i = ref i := hrun i hi
  exact ⟨heq 61 (by decide), heq 44 (by decide), heq 78 (by decide),
    heq 66 (by decide), heq 80 (by decide), heq 36 (by decide)⟩
end DiophantineConsistency.Sign33LiftTerminals
#print axioms DiophantineConsistency.Sign33LiftTerminals.terminals
