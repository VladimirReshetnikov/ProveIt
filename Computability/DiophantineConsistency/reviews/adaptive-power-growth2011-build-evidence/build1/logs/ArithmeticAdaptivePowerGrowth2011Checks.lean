import DiophantineConsistency.ArithmeticAdaptivePowerGrowth2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePowerGrowth2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptivePowerGrowth2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    PowerGrowth currentPorts (fun j => v j+1) := current_natural_power_growth v hz
#print axioms growth_of_facts
#print axioms current_power_growth
#print axioms current_natural_power_growth
end DiophantineConsistency.ArithmeticAdaptivePowerGrowth2011Checks
