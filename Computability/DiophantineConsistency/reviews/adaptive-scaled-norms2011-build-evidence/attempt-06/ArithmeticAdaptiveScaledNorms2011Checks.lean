import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (p : Fin 4 → ℤ) (v : Fin 13 → V) (hz : InternalZero (expressionAt p) v) :
    magnitude (pairEval (rootTerm (factors p).1) v)*magnitude (pairEval (rootTerm (factors p).1) v) +
      (pairEval (rightTerm (factors p).1) v).2 = (pairEval (rightTerm (factors p).1) v).1 :=
  (expressionAt_scaled_norms p v hz).1
#print axioms first_shape
#print axioms main_shape
#print axioms unit_square_norm
#print axioms expressionAt_scaled_norms
end DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011Checks
