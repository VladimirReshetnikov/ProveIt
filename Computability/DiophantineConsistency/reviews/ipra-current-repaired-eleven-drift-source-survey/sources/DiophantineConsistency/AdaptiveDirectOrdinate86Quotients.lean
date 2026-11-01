import DiophantineConsistency.AdaptiveDirectOrdinate86ScaledNorms
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011

/-! Both positive Pell quotients from the actual direct-ordinate zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Quotients
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveQuotients2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86ScaledNorms
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem expressionAt_quotients86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : Quotients p v := by
  have hp := scaled_parameters_positive p v hb hv
  exact quotients_of_scaled_norms p v hp.2.1 hp.2.2.1
    (expressionAt_concrete_scaled_norms86 p v hz)
end DiophantineConsistency.AdaptiveDirectOrdinate86Quotients
