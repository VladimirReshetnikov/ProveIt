import DiophantineConsistency.Sign23CurrentExpressionEval
import DiophantineConsistency.Sign24CurrentExpressionEval
import DiophantineConsistency.Sign23SeedExistential

/-! SOURCE-ONLY: zero existence equivalence for direct sign23 and sign24 expressions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23ExpressionEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed23Octic.seed SharingSeed24Octic.seed CurrentWindowCarry2011.ports
  Sign23CurrentExpression.expression Sign24CurrentExpression.expression

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
    (∃ w : Fin 23 → V, InternalZero Sign23CurrentExpression.expression w) ↔
      ∃ w : Fin 24 → V, InternalZero Sign24CurrentExpression.expression w := by
  have h23 : (∃ w : Fin 23 → V, InternalZero Sign23CurrentExpression.expression w) ↔
      ∃ w : Fin 23 → V, InternalZero (SharingSeed23Octic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign23CurrentExpression.eval_expression]
  have h24 : (∃ w : Fin 24 → V, InternalZero Sign24CurrentExpression.expression w) ↔
      ∃ w : Fin 24 → V, InternalZero (SharingSeed24Octic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
    apply exists_congr
    intro w
    simp only [internalZero_iff, Sign24CurrentExpression.eval_expression]
  have c23 := exists_cons_iff (V := V) (fun v : Fin 24 → V => InternalZero (SharingSeed23Octic.seed CurrentWindowCarry2011.ports) v)
  have c24 := exists_cons_iff (V := V) (fun v : Fin 25 → V => InternalZero (SharingSeed24Octic.seed CurrentWindowCarry2011.ports) v)
  exact h23.trans (c23.trans ((Sign23SeedIff.exists_same_input CurrentWindowCarry2011.ports (1 : V)).trans (c24.symm.trans h24.symm)))
end DiophantineConsistency.Sign23ExpressionEquivalence
#print axioms DiophantineConsistency.Sign23ExpressionEquivalence.exists_cons_iff
#print axioms DiophantineConsistency.Sign23ExpressionEquivalence.zero_exists_iff
