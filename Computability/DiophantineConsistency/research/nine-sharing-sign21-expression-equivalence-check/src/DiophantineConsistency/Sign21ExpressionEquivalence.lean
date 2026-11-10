import DiophantineConsistency.Sign21CurrentExpressionEval
import DiophantineConsistency.Sign22CurrentExpressionEval
import DiophantineConsistency.Sign21SeedExistential

/-! SOURCE-ONLY: zero existence equivalence for direct sign21 and sign22 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed21Degree14.seed SharingSeed22Dodecic.seed CurrentWindowCarry2011.ports
  Sign21CurrentExpression.expression Sign22CurrentExpression.expression

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
    (∃ w : Fin 21 → V, InternalZero Sign21CurrentExpression.expression w) ↔
      ∃ w : Fin 22 → V, InternalZero Sign22CurrentExpression.expression w := by
  have h21 : (∃ w : Fin 21 → V, InternalZero Sign21CurrentExpression.expression w) ↔
      ∃ w : Fin 21 → V, InternalZero (SharingSeed21Degree14.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign21CurrentExpression.eval_expression]
  have h22 : (∃ w : Fin 22 → V, InternalZero Sign22CurrentExpression.expression w) ↔
      ∃ w : Fin 22 → V, InternalZero (SharingSeed22Dodecic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign22CurrentExpression.eval_expression]
  have c21 := exists_cons_iff (V := V) (fun v : Fin 22 → V => InternalZero (SharingSeed21Degree14.seed CurrentWindowCarry2011.ports) v)
  have c22 := exists_cons_iff (V := V) (fun v : Fin 23 → V => InternalZero (SharingSeed22Dodecic.seed CurrentWindowCarry2011.ports) v)
  exact h21.trans (c21.trans ((Sign21SeedIff.exists_same_input CurrentWindowCarry2011.ports (1 : V)).trans (c22.symm.trans h22.symm)))
end DiophantineConsistency.Sign21ExpressionEquivalence
#print axioms DiophantineConsistency.Sign21ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign21ExpressionEquivalence.zero_exists_iff
