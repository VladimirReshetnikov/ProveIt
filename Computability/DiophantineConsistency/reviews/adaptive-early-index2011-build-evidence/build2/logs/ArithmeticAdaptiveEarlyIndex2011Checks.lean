import DiophantineConsistency.ArithmeticAdaptiveEarlyIndex2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveEarlyIndex2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveEarlyIndex2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    EarlyIndex currentPorts (fun j => v j+1) := current_natural_early_index v hz
#print axioms early_index_of_facts
#print axioms expressionAt_early_index
#print axioms current_early_index
#print axioms current_natural_early_index
end DiophantineConsistency.ArithmeticAdaptiveEarlyIndex2011Checks
