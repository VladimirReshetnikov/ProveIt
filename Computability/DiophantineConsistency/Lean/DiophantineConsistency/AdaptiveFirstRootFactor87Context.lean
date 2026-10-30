import DiophantineConsistency.AdaptiveFirstRootFactor87Syntax

/-! Split-natural evaluation respects arbitrary expression substitution, so
the local root identity may be inserted into any one-hole expression context. -/
set_option autoImplicit false
namespace DiophantineConsistency.AdaptiveFirstRootFactor87Context
open DiophantineConsistency.AdaptiveFirstRootFactor87Syntax

variable {σ τ R : Type*} [CommSemiring R]

/-- Equal split values for substituted inputs yield equal split values for the
whole expression, without assuming that the semiring is cancellative. -/
theorem splitEval_subst_congr (e : Expr σ) (f g : σ → Expr τ) (v : τ → R)
    (h : ∀ i, splitEval (f i) v = splitEval (g i) v) :
    splitEval (e.subst f) v = splitEval (e.subst g) v := by
  induction e with
  | constant c => rfl
  | var i => exact h i
  | add p q hp hq =>
      change splitEval (p.subst f + q.subst f) v = splitEval (p.subst g + q.subst g) v
      rw [splitEval_add, splitEval_add, hp, hq]
  | sub p q hp hq =>
      change splitEval (p.subst f - q.subst f) v = splitEval (p.subst g - q.subst g) v
      rw [splitEval_sub, splitEval_sub, hp, hq]
  | mul p q hp hq =>
      change splitEval (p.subst f * q.subst f) v = splitEval (p.subst g * q.subst g) v
      rw [splitEval_mul, splitEval_mul, hp, hq]

def oldFill (q3 qm k bt g y : Expr σ) : Option σ → Expr σ
  | none => oldRoot q3 qm k bt g y
  | some i => .var i

def newFill (q3 qm k bt g y : Expr σ) : Option σ → Expr σ
  | none => newRoot q3 qm k bt g y
  | some i => .var i

/-- The root rewrite has identical split values under any actual syntax context. -/
theorem root_context_split (context : Expr (Option σ))
    (q3 qm k bt g y : Expr σ) (v : σ → R) :
    splitEval (context.subst (oldFill q3 qm k bt g y)) v =
      splitEval (context.subst (newFill q3 qm k bt g y)) v := by
  apply splitEval_subst_congr
  intro i
  cases i with
  | none => exact split_root_identity q3 qm k bt g y v
  | some i => rfl

/-- Hence every one-hole expression's split zero test is preserved. -/
theorem root_context_zero_iff (context : Expr (Option σ))
    (q3 qm k bt g y : Expr σ) (v : σ → R) :
    (splitEval (context.subst (oldFill q3 qm k bt g y)) v).1 =
        (splitEval (context.subst (oldFill q3 qm k bt g y)) v).2 ↔
      (splitEval (context.subst (newFill q3 qm k bt g y)) v).1 =
        (splitEval (context.subst (newFill q3 qm k bt g y)) v).2 := by
  rw [root_context_split]

end DiophantineConsistency.AdaptiveFirstRootFactor87Context
