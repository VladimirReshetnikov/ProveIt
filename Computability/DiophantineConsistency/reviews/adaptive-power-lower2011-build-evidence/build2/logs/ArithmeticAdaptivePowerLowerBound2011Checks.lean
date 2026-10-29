import DiophantineConsistency.ArithmeticAdaptivePowerLowerBound2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePowerLowerBound2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptivePowerLowerBound2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) : 16≤v 6+1 :=
  current_natural_X_lower v hz
#print axioms current_X_lower
#print axioms current_natural_X_lower
end DiophantineConsistency.ArithmeticAdaptivePowerLowerBound2011Checks
