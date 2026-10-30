import DiophantineConsistency.AdaptiveDirectOrdinate86Literal

/-! Relate the shared 14-slot literal context to ordinary 13-slot valuations. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Lift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Literal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {σ τ : Type*}

/-- Substituting only variables is exactly valuation reindexing. -/
theorem splitEval_subst_var (e : Expr σ) (f : σ → τ) (v : τ → V) :
    splitEval (e.subst (fun i => .var (f i))) v = splitEval e (fun i => v (f i)) := by
  induction e with
  | constant c => rfl
  | var i => rfl
  | add a b ha hb =>
      change splitEval (a.subst (fun i => .var (f i)) + b.subst (fun i => .var (f i))) v = splitEval (a+b) (fun i => v (f i))
      rw [splitEval_add, splitEval_add, ha, hb]
  | sub a b ha hb =>
      change splitEval (a.subst (fun i => .var (f i)) - b.subst (fun i => .var (f i))) v = splitEval (a-b) (fun i => v (f i))
      rw [splitEval_sub, splitEval_sub, ha, hb]
  | mul a b ha hb =>
      change splitEval (a.subst (fun i => .var (f i)) * b.subst (fun i => .var (f i))) v = splitEval (a*b) (fun i => v (f i))
      rw [splitEval_mul, splitEval_mul, ha, hb]

def oldIndex (i : Fin 13) : Fin 14 := if i = 11 then 13 else embed i

theorem oldLift_is_var (i : Fin 13) : oldLift i = .var (oldIndex i) := by
  by_cases h : i=11 <;> simp [oldLift,oldIndex,h]

theorem old_lift_eval (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    splitEval ((AdaptiveFirstRootFactor87Literal.expressionAt87 p).subst oldLift) v =
      splitEval (AdaptiveFirstRootFactor87Literal.expressionAt87 p) (fun i => v (oldIndex i)) := by
  have he : oldLift = fun i => .var (oldIndex i) := funext oldLift_is_var
  rw [he]
  exact splitEval_subst_var _ oldIndex v

theorem new_lift_eval (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    splitEval ((expressionAt86 p).subst newLift) v =
      splitEval (expressionAt86 p) (fun i => v (embed i)) := by
  exact splitEval_subst_var _ embed v

/-- Conditional literal equivalence on ordinary 13-coordinate valuations. -/
theorem conditional_unshifted_zero_iff (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (h : ArithmeticSignedPairs.Equivalent (splitEval (oldSquare p) v) (splitEval newSquare v)) :
    AdaptiveEquationSyntax2011.InternalZero
        (AdaptiveFirstRootFactor87Literal.expressionAt87 p) (fun i => v (oldIndex i)) ↔
      AdaptiveEquationSyntax2011.InternalZero (expressionAt86 p) (fun i => v (embed i)) := by
  have he := conditional_literal_zero_iff p v h
  rw [old_lift_eval,new_lift_eval] at he
  exact he

end DiophantineConsistency.AdaptiveDirectOrdinate86Lift
