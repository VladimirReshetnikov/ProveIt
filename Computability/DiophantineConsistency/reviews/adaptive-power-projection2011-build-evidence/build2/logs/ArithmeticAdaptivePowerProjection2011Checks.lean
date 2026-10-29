import DiophantineConsistency.ArithmeticAdaptivePowerProjection2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePowerProjection2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptivePowerProjection2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Projection currentPorts (fun j => v j+1) := current_natural_projection v hz
#print axioms projection_of_facts
#print axioms expressionAt_projection
#print axioms current_projection
#print axioms current_natural_projection
end DiophantineConsistency.ArithmeticAdaptivePowerProjection2011Checks
