import DiophantineConsistency.Sign26CurrentExpressionEval
import DiophantineConsistency.Sign27CurrentExpressionEval
import DiophantineConsistency.Sign26CurrentSeedIff

/-! SOURCE-ONLY: zero existence equivalence for direct sign26 and sign27 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed26Sextic.seed SharingSeed27Sextic.seed CurrentWindowCarry2011.ports
  Sign26CurrentExpression.expression Sign27CurrentExpression.expression

theorem exists_cons_iff {n : ℕ} (P : (Fin (n + 1) → V) → Prop) :
    (∃ w : Fin n → V, P (Fin.cons (1 : V) w)) ↔
      ∃ v : Fin (n + 1) → V, v 0 = 1 ∧ P v := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨Fin.cons 1 w, rfl, hw⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨Fin.tail v, ?_⟩
    have hcons : Fin.cons (1 : V) (Fin.tail v) = v := by
      simpa only [hv] using (Fin.cons_self_tail v)
    simpa only [hcons] using h

theorem zero_exists_iff :
    (∃ w : Fin 26 → V, InternalZero Sign26CurrentExpression.expression w) ↔
      ∃ w : Fin 27 → V, InternalZero Sign27CurrentExpression.expression w := by
  have h26 : (∃ w : Fin 26 → V, InternalZero Sign26CurrentExpression.expression w) ↔
      ∃ w : Fin 26 → V, InternalZero (SharingSeed26Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign26CurrentExpression.eval_expression]
  have h27 : (∃ w : Fin 27 → V, InternalZero Sign27CurrentExpression.expression w) ↔
      ∃ w : Fin 27 → V, InternalZero (SharingSeed27Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign27CurrentExpression.eval_expression]
  have c26 := exists_cons_iff (V := V) (fun v : Fin 27 → V => InternalZero (SharingSeed26Sextic.seed CurrentWindowCarry2011.ports) v)
  have c27 := exists_cons_iff (V := V) (fun v : Fin 28 → V => InternalZero (SharingSeed27Sextic.seed CurrentWindowCarry2011.ports) v)
  exact h26.trans (c26.trans ((Sign26CurrentSeedIff.exists_same_input (1 : V)).trans (c27.symm.trans h27.symm)))
end DiophantineConsistency.Sign26ExpressionEquivalence
#print axioms DiophantineConsistency.Sign26ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign26ExpressionEquivalence.zero_exists_iff
