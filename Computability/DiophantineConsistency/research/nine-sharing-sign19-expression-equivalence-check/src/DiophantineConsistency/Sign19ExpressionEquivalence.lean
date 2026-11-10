import DiophantineConsistency.Sign19CurrentExpressionEval
import DiophantineConsistency.Sign20CurrentExpressionEval
import DiophantineConsistency.Sign19CurrentSeedIff

/-! SOURCE-ONLY: zero existence equivalence for direct sign19 and sign20 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign19ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed19Degree44.seed SharingSeed20Degree20.seed CurrentWindowCarry2011.ports
  Sign19CurrentExpression.expression Sign20CurrentExpression.expression

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
    (∃ w : Fin 19 → V, InternalZero Sign19CurrentExpression.expression w) ↔
      ∃ w : Fin 20 → V, InternalZero Sign20CurrentExpression.expression w := by
  have h19 : (∃ w : Fin 19 → V, InternalZero Sign19CurrentExpression.expression w) ↔
      ∃ w : Fin 19 → V, InternalZero (SharingSeed19Degree44.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign19CurrentExpression.eval_expression]
  have h20 : (∃ w : Fin 20 → V, InternalZero Sign20CurrentExpression.expression w) ↔
      ∃ w : Fin 20 → V, InternalZero (SharingSeed20Degree20.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign20CurrentExpression.eval_expression]
  have c19 := exists_cons_iff (V := V) (fun v : Fin 20 → V => InternalZero (SharingSeed19Degree44.seed CurrentWindowCarry2011.ports) v)
  have c20 := exists_cons_iff (V := V) (fun v : Fin 21 → V => InternalZero (SharingSeed20Degree20.seed CurrentWindowCarry2011.ports) v)
  exact h19.trans (c19.trans ((Sign19CurrentSeedIff.exists_same_input (1 : V)).trans (c20.symm.trans h20.symm)))
end DiophantineConsistency.Sign19ExpressionEquivalence
#print axioms DiophantineConsistency.Sign19ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign19ExpressionEquivalence.zero_exists_iff
