import DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveRankCongruence2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    RankCongruence currentPorts (fun j => v j+1) := current_natural_rank_congruence v hz
#print axioms expressionAt_rank_congruence
#print axioms current_rank_congruence
#print axioms current_natural_rank_congruence
end DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011Checks
