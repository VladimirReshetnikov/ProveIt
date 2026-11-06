import DiophantineConsistency.Norm38ReferenceBase

/-! Proposed initial static/reference agreement; no full model bridge. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel SharingNormTrace SharingTopology38
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Candidate initial agreement for natural ports and positively shifted inputs. -/
theorem initial_agreement (ports : Fin 4 → V) (w : Fin 38 → V) :
    ∀ i ∈ initialNodes,
      pairValue ι (NormAssignment38.assignment ports w i) =
        reference (fun j => ι (ports j))
          (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) i := by
  intro i hi
  fin_cases i <;> simp_all [initialNodes, reference, NormAssignment38.assignment,
    pairValue, map_add, map_one, map_ofNat]

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.initial_agreement
