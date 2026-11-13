import DiophantineConsistency.Sign15CurrentExpressionEval
import DiophantineConsistency.Sign16CurrentExpressionEval
import DiophantineConsistency.Sign15CurrentSeedIff

/-! SOURCE-ONLY: zero existence equivalence for direct sign15 and sign16 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed15Degree124.seed SharingSeed16Degree112.seed CurrentWindowCarry2011.ports
  Sign15CurrentExpression.expression Sign16CurrentExpression.expression

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
    (∃ w : Fin 15 → V, InternalZero Sign15CurrentExpression.expression w) ↔
      ∃ w : Fin 16 → V, InternalZero Sign16CurrentExpression.expression w := by
  have h15 : (∃ w : Fin 15 → V, InternalZero Sign15CurrentExpression.expression w) ↔
      ∃ w : Fin 15 → V, InternalZero (SharingSeed15Degree124.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign15CurrentExpression.eval_expression]
  have h16 : (∃ w : Fin 16 → V, InternalZero Sign16CurrentExpression.expression w) ↔
      ∃ w : Fin 16 → V, InternalZero (SharingSeed16Degree112.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign16CurrentExpression.eval_expression]
  have c15 := exists_cons_iff (V := V) (fun v : Fin 16 → V => InternalZero (SharingSeed15Degree124.seed CurrentWindowCarry2011.ports) v)
  have c16 := exists_cons_iff (V := V) (fun v : Fin 17 → V => InternalZero (SharingSeed16Degree112.seed CurrentWindowCarry2011.ports) v)
  exact h15.trans (c15.trans ((Sign15CurrentSeedIff.exists_same_input (1 : V)).trans (c16.symm.trans h16.symm)))
end DiophantineConsistency.Sign15ExpressionEquivalence
#print axioms DiophantineConsistency.Sign15ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign15ExpressionEquivalence.zero_exists_iff
