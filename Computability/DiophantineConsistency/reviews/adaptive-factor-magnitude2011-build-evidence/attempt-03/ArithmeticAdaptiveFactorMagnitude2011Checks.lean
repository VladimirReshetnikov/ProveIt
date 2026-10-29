import DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011

set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (p : Fin 4 → ℤ) (v : Fin 13 → V) (hz : InternalZero (expressionAt p) v) :
    magnitude (pairEval (factors p).1 v)=1 ∧
    magnitude (pairEval (factors p).2.1 v)=1 ∧
    magnitude (pairEval (factors p).2.2.1 v)=1 ∧
    magnitude (pairEval (factors p).2.2.2 v)=1 := expressionAt_factor_magnitudes p v hz

example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    magnitude (pairEval (factors CurrentWindowCarry2011.ports).1 (fun j => v j+1))=1 :=
  (current_natural_factor_magnitudes v hz).1

#print axioms expression_factors
#print axioms expressionAt_factor_magnitudes
#print axioms current_factor_magnitudes
#print axioms current_natural_factor_magnitudes
end DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011Checks
