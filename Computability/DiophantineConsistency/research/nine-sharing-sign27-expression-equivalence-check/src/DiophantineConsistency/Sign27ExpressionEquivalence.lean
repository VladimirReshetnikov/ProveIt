import DiophantineConsistency.Sign27CurrentExpressionEval
import DiophantineConsistency.Sign28CurrentExpressionEval
import DiophantineConsistency.Sign27SeedExistential

/-! SOURCE-ONLY: zero existence equivalence for direct sign27 and sign28 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed27Sextic.seed SharingSeed28Sextic.seed CurrentWindowCarry2011.ports
  Sign27CurrentExpression.expression Sign28CurrentExpression.expression

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
    (∃ w : Fin 27 → V, InternalZero Sign27CurrentExpression.expression w) ↔
      ∃ w : Fin 28 → V, InternalZero Sign28CurrentExpression.expression w := by
  have h27 : (∃ w : Fin 27 → V, InternalZero Sign27CurrentExpression.expression w) ↔
      ∃ w : Fin 27 → V, InternalZero (SharingSeed27Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign27CurrentExpression.eval_expression]
  have h28 : (∃ w : Fin 28 → V, InternalZero Sign28CurrentExpression.expression w) ↔
      ∃ w : Fin 28 → V, InternalZero (SharingSeed28Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign28CurrentExpression.eval_expression]
  have c27 := exists_cons_iff (V := V) (fun v : Fin 28 → V => InternalZero (SharingSeed27Sextic.seed CurrentWindowCarry2011.ports) v)
  have c28 := exists_cons_iff (V := V) (fun v : Fin 29 → V => InternalZero (SharingSeed28Sextic.seed CurrentWindowCarry2011.ports) v)
  exact h27.trans (c27.trans ((Sign27SeedIff.exists_same_input CurrentWindowCarry2011.ports (1 : V)).trans (c28.symm.trans h28.symm)))
end DiophantineConsistency.Sign27ExpressionEquivalence
#print axioms DiophantineConsistency.Sign27ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign27ExpressionEquivalence.zero_exists_iff
