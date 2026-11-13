import DiophantineConsistency.Sign17CurrentExpressionEval
import DiophantineConsistency.Sign18CurrentExpressionEval
import DiophantineConsistency.Sign17CurrentSeedIff

/-! SOURCE-ONLY: zero existence equivalence for direct sign17 and sign18 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed17Degree96.seed SharingSeed18Degree94.seed CurrentWindowCarry2011.ports
  Sign17CurrentExpression.expression Sign18CurrentExpression.expression

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
    (∃ w : Fin 17 → V, InternalZero Sign17CurrentExpression.expression w) ↔
      ∃ w : Fin 18 → V, InternalZero Sign18CurrentExpression.expression w := by
  have h17 : (∃ w : Fin 17 → V, InternalZero Sign17CurrentExpression.expression w) ↔
      ∃ w : Fin 17 → V, InternalZero (SharingSeed17Degree96.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign17CurrentExpression.eval_expression]
  have h18 : (∃ w : Fin 18 → V, InternalZero Sign18CurrentExpression.expression w) ↔
      ∃ w : Fin 18 → V, InternalZero (SharingSeed18Degree94.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign18CurrentExpression.eval_expression]
  have c17 := exists_cons_iff (V := V) (fun v : Fin 18 → V => InternalZero (SharingSeed17Degree96.seed CurrentWindowCarry2011.ports) v)
  have c18 := exists_cons_iff (V := V) (fun v : Fin 19 → V => InternalZero (SharingSeed18Degree94.seed CurrentWindowCarry2011.ports) v)
  exact h17.trans (c17.trans ((Sign17CurrentSeedIff.exists_same_input (1 : V)).trans (c18.symm.trans h18.symm)))
end DiophantineConsistency.Sign17ExpressionEquivalence
#print axioms DiophantineConsistency.Sign17ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign17ExpressionEquivalence.zero_exists_iff
