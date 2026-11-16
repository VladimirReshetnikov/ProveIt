import PA194PAeqCompleteSupplier
import PA194TransportSentence
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqBind PA194PAeqTermBlueprint
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem isigma1_proves_axiom_supplier :
    𝗜𝚺₁ ⊢ axiomSupplierSentence 𝗣𝗔 ordinaryPAeq := by
  apply Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro V _ _
  exact (axiomSupplier_iff 𝗣𝗔 ordinaryPAeq).mpr (pa_axiom_supplier (V := V))
noncomputable def refutationTransportSentence : ArithmeticSentence :=
  “∀ p, !qqFalsumDef p → (!(provable 𝗣𝗔) p → !(provable ordinaryPAeq) p)”

theorem isigma1_proves_refutation_transport : 𝗜𝚺₁ ⊢ refutationTransportSentence := by
  apply Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro V _ _
  simp [refutationTransportSentence,models_iff,Matrix.comp_vecCons'']
  intro hpa
  exact pa_refutation_to_ordinary hpa
#print axioms isigma1_proves_refutation_transport
#print axioms isigma1_proves_axiom_supplier
end PA194PAeq.InductionReopen
