import DiophantineConsistency.ArithmeticAdaptivePellIndices2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePellIndices2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptivePellIndices2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Indices currentPorts (fun j => v j+1) := current_natural_indices v hz
#print axioms indices_of_quotients
#print axioms expressionAt_indices
#print axioms current_indices
#print axioms current_natural_indices
end DiophantineConsistency.ArithmeticAdaptivePellIndices2011Checks
