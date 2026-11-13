import DiophantineConsistency.Sign32DirectExpressionSplit

/-! UNCOMPILED source-zero composition from the checked generic substitution. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32DirectExpressionSplit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_current :
    (∃ w : Fin 32 → V, InternalZero expression w) ↔
      ∃ u : Fin 14 → V, ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  have hleft : (∃ w : Fin 32 → V, InternalZero expression w) ↔
      ∃ w : Fin 32 → V, InternalZero (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, eval_expression]
  exact hleft.trans Sign32CurrentSourceIff.seed_exists_iff_source
end DiophantineConsistency.Sign32DirectExpressionSplit
#print axioms DiophantineConsistency.Sign32DirectExpressionSplit.zero_iff_current
