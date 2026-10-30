import DiophantineConsistency.ArithmeticRepresentation
import Mathlib.Tactic.Ring

/-!
# Splitting integer syntax into two natural-coefficient expressions

The CRT certificate takes equality of natural polynomials. This executable
translation supplies those two expressions directly from integer syntax,
without choosing a representation from `IsPoly` or `Dioph`.
-/

namespace DiophantineConsistency

/-- Arithmetic syntax using only natural constants, addition and multiplication. -/
inductive NatExpr (σ : Type*)
  | constant (value : ℕ)
  | var (index : σ)
  | add (left right : NatExpr σ)
  | mul (left right : NatExpr σ)
  deriving Repr, DecidableEq

namespace NatExpr

variable {σ : Type*}

instance (n : ℕ) : OfNat (NatExpr σ) n := ⟨constant n⟩
instance : Add (NatExpr σ) := ⟨add⟩
instance : Mul (NatExpr σ) := ⟨mul⟩

/-- The natural expression evaluator is executable. -/
def eval (v : σ → ℕ) : NatExpr σ → ℕ
  | .constant a => a
  | .var i => v i
  | .add p q => p.eval v + q.eval v
  | .mul p q => p.eval v * q.eval v

/-- The corresponding ordinary polynomial has natural coefficients. -/
noncomputable def toPolynomial : NatExpr σ → MvPolynomial σ ℕ
  | .constant a => MvPolynomial.C a
  | .var i => MvPolynomial.X i
  | .add p q => p.toPolynomial + q.toPolynomial
  | .mul p q => p.toPolynomial * q.toPolynomial

@[simp] theorem eval_toPolynomial (e : NatExpr σ) (v : σ → ℕ) :
    MvPolynomial.eval v e.toPolynomial = e.eval v := by
  induction e <;> simp_all [toPolynomial, eval]

/-- Compile natural polynomial evaluation to explicit Diophantine graph data. -/
def graphRep : (e : NatExpr σ) → GraphRep e.eval
  | .constant a => GraphRep.constant a
  | .var i => GraphRep.coordinate i
  | .add p q => GraphRep.add p.graphRep q.graphRep
  | .mul p q => GraphRep.mul p.graphRep q.graphRep

end NatExpr

namespace Expr

variable {σ : Type*}

/-- Supply positive and negative natural expressions by structural recursion. -/
def splitNatural : Expr σ → NatExpr σ × NatExpr σ
  | .constant a => (.constant a.toNat, .constant (-a).toNat)
  | .var i => (.var i, 0)
  | .add p q =>
      let a := p.splitNatural
      let b := q.splitNatural
      (a.1 + b.1, a.2 + b.2)
  | .sub p q =>
      let a := p.splitNatural
      let b := q.splitNatural
      (a.1 + b.2, a.2 + b.1)
  | .mul p q =>
      let a := p.splitNatural
      let b := q.splitNatural
      (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- The difference of the supplied natural values is the original integer value. -/
theorem eval_splitNatural (e : Expr σ) (v : σ → ℕ) :
    (e.splitNatural.1.eval v : ℤ) - e.splitNatural.2.eval v =
      e.eval (fun i => (v i : ℤ)) := by
  induction e with
  | constant a => exact Int.toNat_sub_toNat_neg a
  | var i => simp [splitNatural, NatExpr.eval, eval]
  | add p q hp hq =>
      simp only [splitNatural, NatExpr.eval, Nat.cast_add, eval]
      rw [← hp, ← hq]
      ring
  | sub p q hp hq =>
      simp only [splitNatural, NatExpr.eval, Nat.cast_add, eval]
      rw [← hp, ← hq]
      ring
  | mul p q hp hq =>
      simp only [splitNatural, NatExpr.eval, Nat.cast_add, Nat.cast_mul, eval]
      rw [← hp, ← hq]
      ring

/-- The integer residual vanishes exactly when the two natural values agree. -/
theorem eval_eq_zero_iff_splitNatural (e : Expr σ) (v : σ → ℕ) :
    e.eval (fun i => (v i : ℤ)) = 0 ↔
      e.splitNatural.1.eval v = e.splitNatural.2.eval v := by
  rw [← eval_splitNatural, sub_eq_zero, Int.natCast_inj]

end Expr

namespace Rep

variable {σ : Type*} {P : (σ → ℕ) → Prop}

/-- An explicit integer representation directly supplies the natural equality
required by the CRT certificate, without any new witnesses. -/
theorem correct_splitNatural (r : Rep σ P) (v : σ → ℕ) :
    P v ↔ ∃ w : Fin r.witnessCount → ℕ,
      r.expression.splitNatural.1.eval (Sum.elim v w) =
        r.expression.splitNatural.2.eval (Sum.elim v w) := by
  rw [r.correct]
  apply exists_congr
  intro w
  have ha : natAssignment v w = fun i => ((Sum.elim v w i : ℕ) : ℤ) := by
    funext i
    cases i <;> rfl
  rw [ha]
  exact Expr.eval_eq_zero_iff_splitNatural _ _

end Rep

end DiophantineConsistency
