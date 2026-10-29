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
example (v : Fin 13 → V) (hz : InternalZero expression v) : ScaledNorms currentPorts v :=
  current_scaled_norms v hz
example (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    ScaledNorms currentPorts (fun j => v j+1) := current_natural_scaled_norms v hz
example (p : Fin 4 → ℕ) (v : Fin 13 → V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    0 < v 7*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))) :=
  (scaled_parameters_positive p v hb hv).2.2.1
#print axioms first_rhs_pair
#print axioms main_rhs_pair
#print axioms expressionAt_concrete_scaled_norms
#print axioms currentPorts_cast
#print axioms current_scaled_norms
#print axioms current_natural_scaled_norms
#print axioms scaled_parameters_positive
#print axioms current_parameters_positive
#print axioms current_natural_parameters_positive
#print axioms first_shape
#print axioms main_shape
#print axioms unit_square_norm
#print axioms expressionAt_scaled_norms
end DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011Checks
