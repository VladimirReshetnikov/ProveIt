import PA194PAeqInductionSupplier
import PA194PAeqPASupplier
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem pa_axiom_supplier_except_finite
    (hfinite : ∀ σ ∈ PeanoMinus, Provable ordinaryPAeq (formulaCode 0 (Encodable.encode σ : V))) :
    ∀ p : V, p ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class → Provable ordinaryPAeq (formulaCode 0 p) :=
  PA194PAeqPASupplier.supplier ordinaryPAeq hfinite induction_supplier

theorem pa_refutation_except_finite
    (hfinite : ∀ σ ∈ PeanoMinus, Provable ordinaryPAeq (formulaCode 0 (Encodable.encode σ : V)))
    (hp : Provable 𝗣𝗔 (qqFalsum : V)) : Provable ordinaryPAeq (qqFalsum : V) :=
  PA194PAeqPASupplier.refutation_transport ordinaryPAeq hfinite induction_supplier hp
#print axioms pa_axiom_supplier_except_finite
#print axioms pa_refutation_except_finite
end PA194PAeq.InductionReopen
