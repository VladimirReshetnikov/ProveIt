import DiophantineConsistency.Sign31CurrentExpressionEval
import DiophantineConsistency.Sign31CurrentSourceIff

/-! UNCOMPILED zero-set composition for the checked 31-coordinate expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31CurrentExpression
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_current :
    (∃ w : Fin 31 → V, InternalZero expression w) ↔
      ∃ u : Fin 14 → V, ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  have hleft : (∃ w : Fin 31 → V, InternalZero expression w) ↔
      ∃ w : Fin 31 → V, InternalZero (SharingSeed31Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, eval_expression]
  exact hleft.trans Sign31CurrentSourceIff.seed_exists_iff_source
end DiophantineConsistency.Sign31CurrentExpression
#print axioms DiophantineConsistency.Sign31CurrentExpression.zero_iff_current
