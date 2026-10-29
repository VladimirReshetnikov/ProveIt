import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveMainOrientation2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    MainOriented currentPorts (fun j => v j+1) := current_natural_main_oriented v hz
#print axioms main_root_rep
#print axioms main_parts_positive
#print axioms expressionAt_main_oriented
#print axioms current_main_oriented
#print axioms current_natural_main_oriented
end DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011Checks
