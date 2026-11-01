import DiophantineConsistency.PositiveOffsetCore

/-! Replacing every variable by x−1 preserves the standard structural
degree bound. Relating this bound to polynomial degree is separate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.PositiveOffsetSyntaxDegree
open PositiveOffsetArithmetic

def syntaxDegree {σ : Type*} : Expr σ → ℕ
  | .constant _ => 0
  | .var _ => 1
  | .add a b | .sub a b => max (syntaxDegree a) (syntaxDegree b)
  | .mul a b => syntaxDegree a + syntaxDegree b

theorem degree_decrement {σ : Type*} (e : Expr σ) :
    syntaxDegree (decrement e) = syntaxDegree e := by
  induction e with
  | constant z => rfl
  | var i => change syntaxDegree (Expr.sub (.var i) (.constant 1)) = 1; rfl
  | add a b ha hb => change max (syntaxDegree (decrement a)) (syntaxDegree (decrement b)) = _; rw [ha,hb]; rfl
  | sub a b ha hb => change max (syntaxDegree (decrement a)) (syntaxDegree (decrement b)) = _; rw [ha,hb]; rfl
  | mul a b ha hb => change syntaxDegree (decrement a) + syntaxDegree (decrement b) = _; rw [ha,hb]; rfl

end DiophantineConsistency.PositiveOffsetSyntaxDegree
