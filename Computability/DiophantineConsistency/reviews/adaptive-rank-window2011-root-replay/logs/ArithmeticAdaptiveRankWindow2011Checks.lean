import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveRankWindow2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveRankWindow2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    RankWindow currentPorts (fun j => v j+1) := current_natural_rank_window v hz
#print axioms scalar_rank_window
#print axioms expressionAt_rank_window
#print axioms current_rank_window
#print axioms current_natural_rank_window
end DiophantineConsistency.ArithmeticAdaptiveRankWindow2011Checks
