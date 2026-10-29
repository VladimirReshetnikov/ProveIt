import DiophantineConsistency.ArithmeticAdaptiveQuotients2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveQuotients2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveQuotients2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (m z n : V) (hm : 0<m) (h : z*z=m*m*n) : ∃ t, z=m*t ∧ t*t=n := scaled_quotient m z n hm h
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) : Quotients currentPorts (fun j => v j+1) := current_natural_quotients v hz
#print axioms scaled_quotient
#print axioms quotients_of_scaled_norms
#print axioms expressionAt_quotients
#print axioms current_quotients
#print axioms current_natural_quotients
end DiophantineConsistency.ArithmeticAdaptiveQuotients2011Checks
