import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveIndexComparison2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Comparison currentPorts (fun j => v j+1) := current_natural_comparison v hz
#print axioms base_mono
#print axioms comparison_of_facts
#print axioms expressionAt_comparison
#print axioms current_comparison
#print axioms current_natural_comparison
end DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011Checks
