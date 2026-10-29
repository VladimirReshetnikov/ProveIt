import DiophantineConsistency.ArithmeticAdaptiveExactIndices2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveExactIndices2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveExactIndices2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    ExactIndices currentPorts (fun j => v j+1) := current_natural_exact_indices v hz
#print axioms exact_indices_of_facts
#print axioms expressionAt_exact_indices
#print axioms current_exact_indices
#print axioms current_natural_exact_indices
end DiophantineConsistency.ArithmeticAdaptiveExactIndices2011Checks
