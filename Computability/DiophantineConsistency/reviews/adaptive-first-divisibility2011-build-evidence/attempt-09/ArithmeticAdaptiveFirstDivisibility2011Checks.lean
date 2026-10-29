import DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveFirstDivisibility2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    let w := fun j => v j+1
    ∃ s : V, 0<s ∧ w 7 =
      ((1+w 0*(CurrentMasks2011.beta:V))*
        ((1+w 0*(CurrentMasks2011.beta:V))*(1+w 0*(CurrentMasks2011.beta:V))))*s :=
  current_natural_Y_quotient v hz
#print axioms quotient_forces_Y_divisible
#print axioms expressionAt_Y_quotient
#print axioms current_Y_quotient
#print axioms current_natural_Y_quotient
#print axioms first_root_rep
end DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011Checks
