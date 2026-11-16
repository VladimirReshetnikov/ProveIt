import PA194OrdinarySentenceEnvironment
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ClosedEnvironment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194PAeqBind PA194FormulaDispatcher PA194ForwardTyped
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory SourceL) [T.Δ₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem ordinaryAxiom_packet_of_root {p param n d : V}
    (hp : IsUFormula PA194PAeq.language p) (ha : p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class)
    (hparam : ParametersValid 0 n param)
    (hroot : Provable T (translateFormula (rootParameters d) p)) :
    Provable T (translateFormula param p) := by
  rw [←ordinaryAxiom_root_packet hp ha hparam]
  exact hroot

theorem ordinaryAxiom_packet_of_root_supply {param n : V} (hparam : ParametersValid 0 n param)
    (hroot : ∀ p : V, IsUFormula PA194PAeq.language p → p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class →
      Provable T (translateFormula (rootParameters p) p)) :
    ∀ p : V, IsUFormula PA194PAeq.language p → p ∈ PA194PAeq.ordinaryPAeq.Δ₁Class →
      Provable T (translateFormula param p) := by
  intro p hp ha
  exact ordinaryAxiom_packet_of_root T hp ha hparam (hroot p hp ha)
#print axioms ordinaryAxiom_packet_of_root
#print axioms ordinaryAxiom_packet_of_root_supply
end generic
end PA194ClosedEnvironment
