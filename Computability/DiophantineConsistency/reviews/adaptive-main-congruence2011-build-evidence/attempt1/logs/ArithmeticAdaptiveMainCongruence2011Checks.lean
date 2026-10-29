import DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveMainCongruence2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    MainCongruence currentPorts (fun j => v j+1) := current_natural_main_congruence v hz
#print axioms expressionAt_main_congruence
#print axioms current_main_congruence
#print axioms current_natural_main_congruence
end DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011Checks
