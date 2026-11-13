import DiophantineConsistency.Norm38ReferenceInitialGroup00
import DiophantineConsistency.Norm38ReferenceInitialGroup01
import DiophantineConsistency.Norm38ReferenceInitialGroup02
import DiophantineConsistency.Norm38ReferenceInitialGroup03
import DiophantineConsistency.Norm38ReferenceInitialGroup04
import DiophantineConsistency.Norm38ReferenceInitialGroup05
import DiophantineConsistency.Norm38ReferenceInitialGroup06

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem initial_agreement (ports : Fin 4 → V) (w : Fin 38 → V) :
    ∀ i ∈ initialNodes,
      pairValue ι (NormAssignment38.assignment ports w i) =
        reference (fun j => ι (ports j))
          (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) i := by
  intro i hi
  change i ∈ (List.finRange 21).map (fun j => Fin.castLE (by decide : 21 ≤ 81) j) at hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  fin_cases j
  · exact initial_node00 ports w
  · exact initial_node01 ports w
  · exact initial_node02 ports w
  · exact initial_node03 ports w
  · exact initial_node04 ports w
  · exact initial_node05 ports w
  · exact initial_node06 ports w
  · exact initial_node07 ports w
  · exact initial_node08 ports w
  · exact initial_node09 ports w
  · exact initial_node10 ports w
  · exact initial_node11 ports w
  · exact initial_node12 ports w
  · exact initial_node13 ports w
  · exact initial_node14 ports w
  · exact initial_node15 ports w
  · exact initial_node16 ports w
  · exact initial_node17 ports w
  · exact initial_node18 ports w
  · exact initial_node19 ports w
  · exact initial_node20 ports w

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.initial_agreement
