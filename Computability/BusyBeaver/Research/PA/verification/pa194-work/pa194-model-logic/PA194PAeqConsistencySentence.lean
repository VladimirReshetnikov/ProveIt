import PA194PAeqSupplierSentence
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqBind PA194PAeqTermBlueprint
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
noncomputable def ordinaryRefutationSentence : ArithmeticSentence :=
  “∃ p, !qqFalsumDef p ∧ !(provable ordinaryPAeq) p”
noncomputable def paRefutationSentence : ArithmeticSentence :=
  “∃ p, !qqFalsumDef p ∧ !(provable 𝗣𝗔) p”
noncomputable def ordinaryConsistencySentence : ArithmeticSentence := ∼ordinaryRefutationSentence
noncomputable def paConsistencySentence : ArithmeticSentence := ∼paRefutationSentence

theorem isigma1_proves_consistency_transfer :
    𝗜𝚺₁ ⊢ ordinaryConsistencySentence 🡒 paConsistencySentence := by
  apply Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro V _ _
  simp [ordinaryConsistencySentence,paConsistencySentence,ordinaryRefutationSentence,paRefutationSentence,models_iff]
  intro hOrd x
  by_cases hx : x = (qqFalsum : V)
  · subst x
    right
    intro hPA
    have ho := hOrd (qqFalsum : V)
    simp only [not_true_eq_false,eq_self_iff_true,false_or] at ho
    exact ho (pa_refutation_to_ordinary hPA)
  · exact Or.inl hx
#print axioms isigma1_proves_consistency_transfer
end PA194PAeq.InductionReopen
