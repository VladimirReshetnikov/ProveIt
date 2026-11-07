import DiophantineConsistency.Sign28CurrentExpressionEval
import DiophantineConsistency.Sign31CurrentExpressionEval
import DiophantineConsistency.Sign28CurrentConsIff

/-! SOURCE-ONLY: model-level zero existence equivalence for direct expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed28Sextic.seed SharingSeed31Sextic.seed CurrentWindowCarry2011.ports
  Sign28CurrentExpression.expression Sign31CurrentExpression.expression

theorem zero_exists_iff :
    (∃ w : Fin 28 → V, InternalZero Sign28CurrentExpression.expression w) ↔
      ∃ w : Fin 31 → V, InternalZero Sign31CurrentExpression.expression w := by
  have h28 : (∃ w : Fin 28 → V, InternalZero Sign28CurrentExpression.expression w) ↔
      ∃ w : Fin 28 → V, InternalZero (SharingSeed28Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign28CurrentExpression.eval_expression]
  have h31 : (∃ w : Fin 31 → V, InternalZero Sign31CurrentExpression.expression w) ↔
      ∃ w : Fin 31 → V, InternalZero (SharingSeed31Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign31CurrentExpression.eval_expression]
  exact h28.trans ((Sign28CurrentConsIff.seed_cons_iff (V := V)).trans h31.symm)
end DiophantineConsistency.Sign28ExpressionEquivalence
#print axioms DiophantineConsistency.Sign28ExpressionEquivalence.zero_exists_iff
