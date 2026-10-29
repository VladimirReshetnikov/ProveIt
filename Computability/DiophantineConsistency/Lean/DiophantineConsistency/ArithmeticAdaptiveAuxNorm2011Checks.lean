import DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveAuxNorm2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    AuxNorm currentPorts (fun j => v j+1) := current_natural_aux_norm v hz
#print axioms expressionAt_aux_norm
#print axioms current_aux_norm
#print axioms current_natural_aux_norm
end DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011Checks
