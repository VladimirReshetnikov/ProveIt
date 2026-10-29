import DiophantineConsistency.ArithmeticAdaptiveWindow2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveWindow2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticWindowInterface ArithmeticAdaptiveWindow2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    ∃ N W C F : V, Window N W C F := current_natural_window v hz
#print axioms current_window
#print axioms current_natural_window
end DiophantineConsistency.ArithmeticAdaptiveWindow2011Checks
