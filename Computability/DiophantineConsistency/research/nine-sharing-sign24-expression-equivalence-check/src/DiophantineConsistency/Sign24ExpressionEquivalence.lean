import DiophantineConsistency.Sign24CurrentExpressionEval
import DiophantineConsistency.Sign25CurrentExpressionEval
import DiophantineConsistency.Sign24CurrentSeedIff

/-! SOURCE-ONLY: zero existence equivalence for direct sign24 and sign25 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed24Octic.seed SharingSeed25Octic.seed CurrentWindowCarry2011.ports
  Sign24CurrentExpression.expression Sign25CurrentExpression.expression

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
    (∃ w : Fin 24 → V, InternalZero Sign24CurrentExpression.expression w) ↔
      ∃ w : Fin 25 → V, InternalZero Sign25CurrentExpression.expression w := by
  have h24 : (∃ w : Fin 24 → V, InternalZero Sign24CurrentExpression.expression w) ↔
      ∃ w : Fin 24 → V, InternalZero (SharingSeed24Octic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign24CurrentExpression.eval_expression]
  have h25 : (∃ w : Fin 25 → V, InternalZero Sign25CurrentExpression.expression w) ↔
      ∃ w : Fin 25 → V, InternalZero (SharingSeed25Octic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign25CurrentExpression.eval_expression]
  have c24 := exists_cons_iff (V := V) (fun v : Fin 25 → V => InternalZero (SharingSeed24Octic.seed CurrentWindowCarry2011.ports) v)
  have c25 := exists_cons_iff (V := V) (fun v : Fin 26 → V => InternalZero (SharingSeed25Octic.seed CurrentWindowCarry2011.ports) v)
  exact h24.trans (c24.trans ((Sign24CurrentSeedIff.exists_same_input (1 : V)).trans (c25.symm.trans h25.symm)))
end DiophantineConsistency.Sign24ExpressionEquivalence
#print axioms DiophantineConsistency.Sign24ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign24ExpressionEquivalence.zero_exists_iff
