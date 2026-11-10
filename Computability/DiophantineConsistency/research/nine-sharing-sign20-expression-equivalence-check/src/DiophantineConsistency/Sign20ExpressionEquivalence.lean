import DiophantineConsistency.Sign20CurrentExpressionEval
import DiophantineConsistency.Sign21CurrentExpressionEval
import DiophantineConsistency.Sign20CurrentSeedIff

/-! SOURCE-ONLY: zero existence equivalence for direct sign20 and sign21 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed20Degree20.seed SharingSeed21Degree14.seed CurrentWindowCarry2011.ports
  Sign20CurrentExpression.expression Sign21CurrentExpression.expression

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
    (∃ w : Fin 20 → V, InternalZero Sign20CurrentExpression.expression w) ↔
      ∃ w : Fin 21 → V, InternalZero Sign21CurrentExpression.expression w := by
  have h20 : (∃ w : Fin 20 → V, InternalZero Sign20CurrentExpression.expression w) ↔
      ∃ w : Fin 20 → V, InternalZero (SharingSeed20Degree20.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign20CurrentExpression.eval_expression]
  have h21 : (∃ w : Fin 21 → V, InternalZero Sign21CurrentExpression.expression w) ↔
      ∃ w : Fin 21 → V, InternalZero (SharingSeed21Degree14.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign21CurrentExpression.eval_expression]
  have c20 := exists_cons_iff (V := V) (fun v : Fin 21 → V => InternalZero (SharingSeed20Degree20.seed CurrentWindowCarry2011.ports) v)
  have c21 := exists_cons_iff (V := V) (fun v : Fin 22 → V => InternalZero (SharingSeed21Degree14.seed CurrentWindowCarry2011.ports) v)
  exact h20.trans (c20.trans ((Sign20CurrentSeedIff.exists_same_input (1 : V)).trans (c21.symm.trans h21.symm)))
end DiophantineConsistency.Sign20ExpressionEquivalence
#print axioms DiophantineConsistency.Sign20ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign20ExpressionEquivalence.zero_exists_iff
