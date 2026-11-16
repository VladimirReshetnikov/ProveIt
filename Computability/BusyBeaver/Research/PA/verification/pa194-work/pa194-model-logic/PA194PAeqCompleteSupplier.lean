import PA194PAeqFiniteSupplier
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem pa_axiom_supplier : ∀ p : V, p ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class →
    Provable ordinaryPAeq (formulaCode 0 p) :=
  pa_axiom_supplier_except_finite finite_supplier
#print axioms pa_axiom_supplier
end PA194PAeq.InductionReopen
