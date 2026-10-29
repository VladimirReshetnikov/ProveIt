import DiophantineConsistency.ArithmeticAdaptiveRadix2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveRadix2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveRadix2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Radix (fun j => v j+1) := current_natural_radix v hz
#print axioms current_radix
#print axioms current_natural_radix
end DiophantineConsistency.ArithmeticAdaptiveRadix2011Checks
