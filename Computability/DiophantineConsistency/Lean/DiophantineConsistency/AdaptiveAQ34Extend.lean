import DiophantineConsistency.AdaptiveAQ34Rest
import DiophantineConsistency.AdaptiveAQ34Literal
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ34Extend
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveAQ34Literal AdaptiveAQ34Context AdaptiveAQ34Maps AdaptiveAQ34Rest
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem extend_inputs (v : Fin 34 → V) : ∀ i, Equivalent (splitEval (oldFill i) (extend v)) (splitEval (newFill i) v) := by
  intro i
  cases i with
  | inl i =>
    fin_cases i <;> simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend,HSub.hSub,Sub.sub,add_comm]
  | inr i =>
    simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend_rest]

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    InternalZero (AdaptiveAQ35Literal.literal p) (extend v) ↔ InternalZero (AdaptiveAQ34Literal.literal p) v := by
  rw [← old_literal, ← new_literal]
  exact equivalent_zero_iff (subst_equiv_hetero (sum p) oldFill newFill (extend v) v (extend_inputs v))
#print axioms extend_zero
end DiophantineConsistency.AdaptiveAQ34Extend
