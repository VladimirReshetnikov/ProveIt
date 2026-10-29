import DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveStrongNorm2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    StrongNorm (fun j => v j+1) := current_natural_strong_norm v hz
#print axioms strong_rep
#print axioms expressionAt_strong_norm
#print axioms current_strong_norm
#print axioms current_natural_strong_norm
end DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011Checks
