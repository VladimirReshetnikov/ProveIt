import PA194PAeqInductionAddOne
import PA194PAeqInductionAxiomProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionAddOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem primitiveBody_provable_if_zero_free {p : V} (hp : IsSemiformula language 1 p)
    (hfree : formulaFreeBound (inductionBody p) = 0) :
    Provable ordinaryPAeq (inductionBody p) := by
  refine ⟨closedInductionProof p, ?_⟩
  have h := closedInductionProof_valid hp
  simpa [closedInduction,fullyClose,hfree] using h

theorem addOneBody_provable_if_zero_free {p : V} (hp : IsSemiformula language 1 p)
    (hfree : formulaFreeBound (inductionBody p) = 0) :
    Provable ordinaryPAeq (inductionBodyAddOne p) :=
  addOneBody_provable hp (primitiveBody_provable_if_zero_free hp hfree)
#print axioms primitiveBody_provable_if_zero_free
#print axioms addOneBody_provable_if_zero_free
end PA194PAeq.InductionAddOne
