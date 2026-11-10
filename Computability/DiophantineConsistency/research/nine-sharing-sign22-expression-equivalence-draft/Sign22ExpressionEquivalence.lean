import DiophantineConsistency.Sign22CurrentExpressionEval
import DiophantineConsistency.Sign23CurrentExpressionEval
import DiophantineConsistency.Sign22SeedExistential

/-! SOURCE-ONLY: zero existence equivalence for direct sign22 and sign23 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed22Dodecic.seed SharingSeed23Octic.seed CurrentWindowCarry2011.ports
  Sign22CurrentExpression.expression Sign23CurrentExpression.expression

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
    (∃ w : Fin 22 → V, InternalZero Sign22CurrentExpression.expression w) ↔
      ∃ w : Fin 23 → V, InternalZero Sign23CurrentExpression.expression w := by
  have h22 : (∃ w : Fin 22 → V, InternalZero Sign22CurrentExpression.expression w) ↔
      ∃ w : Fin 22 → V, InternalZero (SharingSeed22Dodecic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign22CurrentExpression.eval_expression]
  have h23 : (∃ w : Fin 23 → V, InternalZero Sign23CurrentExpression.expression w) ↔
      ∃ w : Fin 23 → V, InternalZero (SharingSeed23Octic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign23CurrentExpression.eval_expression]
  have c22 := exists_cons_iff (V := V) (fun v : Fin 23 → V => InternalZero (SharingSeed22Dodecic.seed CurrentWindowCarry2011.ports) v)
  have c23 := exists_cons_iff (V := V) (fun v : Fin 24 → V => InternalZero (SharingSeed23Octic.seed CurrentWindowCarry2011.ports) v)
  exact h22.trans (c22.trans ((Sign22SeedIff.exists_same_input CurrentWindowCarry2011.ports (1 : V)).trans (c23.symm.trans h23.symm)))
end DiophantineConsistency.Sign22ExpressionEquivalence
#print axioms DiophantineConsistency.Sign22ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign22ExpressionEquivalence.zero_exists_iff
