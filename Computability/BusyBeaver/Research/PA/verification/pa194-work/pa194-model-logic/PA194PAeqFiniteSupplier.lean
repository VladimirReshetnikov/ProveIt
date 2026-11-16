import PA194PAeqFiniteRemainingNext15
import PA194PAeqTriInternal
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem finite_supplier : ∀ σ ∈ PeanoMinus,
    Provable ordinaryPAeq (formulaCode 0 (Encodable.encode σ : V)) := by
  apply finite_supplier_of_remaining_next15
  intro σ hσ
  simp only [remainingFiniteNext15,List.mem_cons,List.not_mem_nil,or_false] at hσ
  subst σ
  simpa only [Sentence.quote_eq_encode] using (TriProof.internal_ltTri_proof (V := V))

theorem pa_refutation_to_ordinary
    (hp : Provable 𝗣𝗔 (qqFalsum : V)) : Provable ordinaryPAeq (qqFalsum : V) :=
  pa_refutation_of_remaining_next15 (fun σ hσ => finite_supplier σ (by
    simp only [remainingFiniteNext15,List.mem_cons,List.not_mem_nil,or_false] at hσ
    subst σ
    exact PeanoMinus.ltTri)) hp
#print axioms finite_supplier
#print axioms pa_refutation_to_ordinary
end PA194PAeq.InductionReopen
