import DiophantineConsistency.AdaptiveZ46Maps
import DiophantineConsistency.AdaptiveDirectOrdinate86Context
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ46Rest
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveZ46Context AdaptiveZ46Maps
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldMasked : Fin 2 ⊕ Fin 44 → Expr (Fin 47)
 | .inl _ => 0
 | .inr i => .var (oldRest i)
def newMasked : Fin 2 ⊕ Fin 44 → Expr (Fin 46)
 | .inl _ => 0
 | .inr i => .var (newRest i)

theorem old_ignore (p : Fin 4 → ℤ) (i : Fin 33) (h0 : i ≠ 0) (h14 : i ≠ 14) :
    (residuals p i).subst oldFill = (residuals p i).subst oldMasked := by
  fin_cases i <;> try {exfalso; exact h0 rfl} <;> try {exfalso; exact h14 rfl} <;> rfl

theorem new_ignore (p : Fin 4 → ℤ) (i : Fin 33) (h0 : i ≠ 0) (h14 : i ≠ 14) :
    (residuals p i).subst newFill = (residuals p i).subst newMasked := by
  fin_cases i <;> try {exfalso; exact h0 rfl} <;> try {exfalso; exact h14 rfl} <;> rfl

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

theorem project_rest_equiv (p : Fin 4 → ℤ) (v : Fin 47 → V) (r : V)
    (i : Fin 33) (h0 : i ≠ 0) (h14 : i ≠ 14) :
    InternalZero ((residuals p i).subst oldFill) v ↔
      InternalZero ((residuals p i).subst newFill) (project v r) := by
  rw [old_ignore p i h0 h14, new_ignore p i h0 h14]
  have h : ∀ j, Equivalent (splitEval (oldMasked j) v) (splitEval (newMasked j) (project v r)) := by
    intro j
    cases j with
    | inl j => exact equivalent_refl _
    | inr j => simp [oldMasked,newMasked,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project_rest]
  exact equivalent_zero_iff (subst_equiv_hetero (residuals p i) oldMasked newMasked v (project v r) h)

theorem extend_rest_equiv (p : Fin 4 → ℤ) (v : Fin 46 → V)
    (i : Fin 33) (h0 : i ≠ 0) (h14 : i ≠ 14) :
    InternalZero ((residuals p i).subst oldFill) (extend v) ↔
      InternalZero ((residuals p i).subst newFill) v := by
  rw [old_ignore p i h0 h14, new_ignore p i h0 h14]
  have h : ∀ j, Equivalent (splitEval (oldMasked j) (extend v)) (splitEval (newMasked j) v) := by
    intro j
    cases j with
    | inl j => exact equivalent_refl _
    | inr j => simp [oldMasked,newMasked,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend_rest]
  exact equivalent_zero_iff (subst_equiv_hetero (residuals p i) oldMasked newMasked (extend v) v h)
#print axioms project_rest_equiv
#print axioms extend_rest_equiv
end DiophantineConsistency.AdaptiveZ46Rest
