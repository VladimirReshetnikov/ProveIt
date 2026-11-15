import PA194PAeqConsistencySentence
import DiophantineConsistency.IPRAPA196Consistency
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqBind PA194PAeqTermBlueprint
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem isigma1_proves_foundation_consistency_transfer :
    𝗜𝚺₁ ⊢ ordinaryConsistencySentence 🡒 DiophantineConsistency.IPRAPA196Consistency.paConsistency := by
  apply Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro V _ _
  simp [ordinaryConsistencySentence,ordinaryRefutationSentence,
    DiophantineConsistency.IPRAPA196Consistency.paConsistency_eq,
    DiophantineConsistency.IPRAPA196Consistency.paRefutation,provabilityPred,models_iff]
  intro hOrd hPA
  have ho := hOrd (qqFalsum : V)
  simp only [not_true_eq_false,false_or] at ho
  apply ho
  apply pa_refutation_to_ordinary
  simpa [Sentence.quote_def] using hPA
theorem isigma1_proves_canonical_consistency_transfer :
    𝗜𝚺₁ ⊢ (PA194PAeq.ordinaryPAeq.consistent : ArithmeticSentence) 🡒
      ((𝗣𝗔 : ArithmeticTheory).consistent : ArithmeticSentence) := by
  apply Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro V _ _
  simp [models_iff, Theory.Consistent, Sentence.quote_def]
  intro hOrd hPA
  exact hOrd (pa_refutation_to_ordinary hPA)
#print axioms isigma1_proves_canonical_consistency_transfer
#print axioms isigma1_proves_foundation_consistency_transfer
end PA194PAeq.InductionReopen
