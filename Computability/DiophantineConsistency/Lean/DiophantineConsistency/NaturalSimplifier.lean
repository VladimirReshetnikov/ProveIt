import DiophantineConsistency.QuarticCompiler

/-!
# Remove redundant natural gates before quartic compilation

Zero and unit operations introduced by signed splitting need no independent
quartic wire. Constant folding and these elementary identities preserve all
natural values and never increase the number of syntax-tree gates.
-/

namespace DiophantineConsistency.NatExpr

open QuarticCompiler

variable {σ : Type*}

def smartAdd (p q : NatExpr σ) : NatExpr σ :=
  match p, q with
  | .constant a, .constant b => .constant (a + b)
  | .constant 0, q => q
  | p, .constant 0 => p
  | _, _ => .add p q

def smartMul (p q : NatExpr σ) : NatExpr σ :=
  match p, q with
  | .constant a, .constant b => .constant (a * b)
  | .constant 0, _ => .constant 0
  | _, .constant 0 => .constant 0
  | .constant 1, q => q
  | p, .constant 1 => p
  | _, _ => .mul p q

theorem eval_smartAdd (p q : NatExpr σ) (v : σ → ℕ) :
    (smartAdd p q).eval v = p.eval v + q.eval v := by
  unfold smartAdd
  split <;> simp [eval]

theorem eval_smartMul (p q : NatExpr σ) (v : σ → ℕ) :
    (smartMul p q).eval v = p.eval v * q.eval v := by
  unfold smartMul
  split <;> simp [eval]

theorem count_smartAdd_le (p q : NatExpr σ) :
    Gates.count (smartAdd p q) ≤ 1 + (Gates.count p + Gates.count q) := by
  unfold smartAdd
  split <;> simp_all [Gates.count] <;> omega

theorem count_smartMul_le (p q : NatExpr σ) :
    Gates.count (smartMul p q) ≤ 1 + (Gates.count p + Gates.count q) := by
  unfold smartMul
  split <;> simp_all [Gates.count] <;> omega

/-- Fold constants and delete zero/unit gates by structural recursion. -/
def simplify : NatExpr σ → NatExpr σ
  | .constant a => .constant a
  | .var i => .var i
  | .add p q => smartAdd p.simplify q.simplify
  | .mul p q => smartMul p.simplify q.simplify

theorem eval_simplify (e : NatExpr σ) (v : σ → ℕ) : e.simplify.eval v = e.eval v := by
  induction e <;> simp_all [simplify, eval_smartAdd, eval_smartMul, eval]

/-- A checked size bound for the exact gates used by `QuarticCompiler`. -/
theorem count_simplify_le (e : NatExpr σ) : Gates.count e.simplify ≤ Gates.count e := by
  induction e with
  | constant a | var i => rfl
  | add p q hp hq =>
      exact (count_smartAdd_le _ _).trans (by simp only [Gates.count]; omega)
  | mul p q hp hq =>
      exact (count_smartMul_le _ _).trans (by simp only [Gates.count]; omega)

end DiophantineConsistency.NatExpr
