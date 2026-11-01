import DiophantineConsistency.AdaptiveAQ40Zeros
import DiophantineConsistency.AdaptiveAQ40Maps
import DiophantineConsistency.AdaptiveAQ40Literal
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ40Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift
open AdaptiveAQ40Context AdaptiveAQ40Maps AdaptiveAQ40Zeros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem subst_equiv_hetero {σ τ υ : Type*} (e : Expr σ) (f : σ → Expr τ) (g : σ → Expr υ)
    (v : τ → V) (w : υ → V)
    (h : ∀ i, Equivalent (splitEval (f i) v) (splitEval (g i) w)) :
    Equivalent (splitEval (e.subst f) v) (splitEval (e.subst g) w) := by
  induction e with
  | constant c => exact equivalent_refl _
  | var i => exact h i
  | add p q hp hq =>
      change Equivalent (splitEval (p.subst f + q.subst f) v) (splitEval (p.subst g + q.subst g) w)
      rw [splitEval_add,splitEval_add]
      exact plus_equiv hp hq
  | sub p q hp hq =>
      change Equivalent (splitEval (p.subst f - q.subst f) v) (splitEval (p.subst g - q.subst g) w)
      rw [splitEval_sub,splitEval_sub]
      exact minus_equiv hp hq
  | mul p q hp hq =>
      change Equivalent (splitEval (p.subst f * q.subst f) v) (splitEval (p.subst g * q.subst g) w)
      rw [splitEval_mul,splitEval_mul]
      exact equivalent_multiply hp hq

theorem old_all {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 39 → Expr σ) (v : σ → V)
    (hz : InternalZero ((oldSum p).subst f) v) :
    ∀ i : Fin 28, InternalZero ((residuals p i).subst f) v := by
  obtain ⟨h0, ht⟩ := (old_zero p f v).mp hz
  exact Fin.cases h0 ht

theorem tail_covers (i : Fin 28) (h0 : i ≠ 0) (h9 : i ≠ 9) :
    ∃ j : Fin 26, tailIndex j = i := by
  have hv0 : i.val ≠ 0 := by intro h; apply h0; apply Fin.ext; simpa using h
  have hv9 : i.val ≠ 9 := by intro h; apply h9; apply Fin.ext; simpa using h
  by_cases h : i.val < 9
  · refine ⟨⟨i.val-1, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [tailIndex]
    split <;> simp_all <;> omega
  · refine ⟨⟨i.val-2, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [tailIndex]
    split <;> simp_all <;> omega

theorem old_relations (p : Fin 4 → ℤ) (v : Fin 42 → V)
    (hz : InternalZero (AdaptiveNamedValues42.literal p) v) :
    v 18 = v 34 + v 7 ∧ v 38 * v 38 + v 41 = v 40 := by
  have hs : InternalZero ((oldSum p).subst oldFill) v := by rw [old_literal]; exact hz
  have all := old_all p oldFill v hs
  have ha := all 9
  have hq := all 3
  change InternalZero ((.var 18) - (.var 34 + .var 7) : Expr (Fin 42)) v at ha
  change InternalZero ((.var 38 * .var 38) - (.var 40 - .var 41) : Expr (Fin 42)) v at hq
  constructor
  · simp only [InternalZero, HSub.hSub, Sub.sub, HAdd.hAdd, Add.add,
      Expr.splitNatural, NatExpr.evalSemiring] at ha
    change v 18 + ((0 : V) + 0) = 0 + (v 34 + v 7) at ha
    simpa only [add_zero, zero_add] using ha
  · simp only [InternalZero, HSub.hSub, Sub.sub, HMul.hMul, Mul.mul,
      Expr.splitNatural, NatExpr.evalSemiring] at hq
    change v 38 * v 38 + (0 : V) * 0 + (0 + v 41) =
      v 38 * 0 + 0 * v 38 + (v 40 + 0) at hq
    simpa only [mul_zero, zero_mul, add_zero, zero_add] using hq
#print axioms old_relations
end DiophantineConsistency.AdaptiveAQ40Transport
