import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace DiophantineConsistency

/-- Integer arithmetic syntax with a specified type of variables. -/
inductive Expr (σ : Type*)
  | constant (value : ℤ)
  | var (index : σ)
  | add (left right : Expr σ)
  | sub (left right : Expr σ)
  | mul (left right : Expr σ)
  deriving Repr, DecidableEq

namespace Expr

variable {σ τ : Type*}

instance (n : ℕ) : OfNat (Expr σ) n := ⟨constant n⟩
instance : Add (Expr σ) := ⟨add⟩
instance : Sub (Expr σ) := ⟨sub⟩
instance : Mul (Expr σ) := ⟨mul⟩
instance : Neg (Expr σ) := ⟨fun e => sub (constant 0) e⟩

/-- Evaluate syntax using integer arithmetic. -/
def eval (v : σ → ℤ) : Expr σ → ℤ
  | .constant a => a
  | .var i => v i
  | .add p q => p.eval v + q.eval v
  | .sub p q => p.eval v - q.eval v
  | .mul p q => p.eval v * q.eval v

@[simp] theorem eval_constant (v : σ → ℤ) (a : ℤ) : (constant a).eval v = a := rfl
@[simp] theorem eval_var (v : σ → ℤ) (i : σ) : (var i).eval v = v i := rfl
@[simp] theorem eval_add (v : σ → ℤ) (p q : Expr σ) :
    (p + q).eval v = p.eval v + q.eval v := rfl
@[simp] theorem eval_sub (v : σ → ℤ) (p q : Expr σ) :
    (p - q).eval v = p.eval v - q.eval v := rfl
@[simp] theorem eval_mul (v : σ → ℤ) (p q : Expr σ) :
    (p * q).eval v = p.eval v * q.eval v := rfl

/-- A fixed natural power is expanded by an executable syntax constructor. -/
def pow (e : Expr σ) : ℕ → Expr σ
  | 0 => .constant 1
  | n + 1 => .mul (e.pow n) e

instance : Pow (Expr σ) ℕ := ⟨pow⟩

@[simp] theorem eval_pow (e : Expr σ) (n : ℕ) (v : σ → ℤ) :
    (e ^ n).eval v = e.eval v ^ n := by
  change (e.pow n).eval v = _
  induction n <;> simp_all [pow, eval, pow_succ]

/-- Rename variables without inspecting their values. -/
def rename (f : σ → τ) : Expr σ → Expr τ
  | .constant a => .constant a
  | .var i => .var (f i)
  | .add p q => .add (p.rename f) (q.rename f)
  | .sub p q => .sub (p.rename f) (q.rename f)
  | .mul p q => .mul (p.rename f) (q.rename f)

@[simp] theorem eval_rename (e : Expr σ) (f : σ → τ) (v : τ → ℤ) :
    (e.rename f).eval v = e.eval (v ∘ f) := by
  induction e <;> simp_all [rename, eval]

/-- Substitute arithmetic expressions for variables. -/
def subst (f : σ → Expr τ) : Expr σ → Expr τ
  | .constant a => .constant a
  | .var i => f i
  | .add p q => .add (p.subst f) (q.subst f)
  | .sub p q => .sub (p.subst f) (q.subst f)
  | .mul p q => .mul (p.subst f) (q.subst f)

@[simp] theorem eval_subst (e : Expr σ) (f : σ → Expr τ) (v : τ → ℤ) :
    (e.subst f).eval v = e.eval (fun i => (f i).eval v) := by
  induction e <;> simp_all [subst, eval]

/-- Interpret the stored syntax as an ordinary integer polynomial.
Only this algebraic interpretation uses Mathlib's noncomputable polynomial
operations; the syntax, its evaluator, and its constructors remain executable. -/
noncomputable def toPolynomial : Expr σ → MvPolynomial σ ℤ
  | .constant a => MvPolynomial.C a
  | .var i => MvPolynomial.X i
  | .add p q => p.toPolynomial + q.toPolynomial
  | .sub p q => p.toPolynomial - q.toPolynomial
  | .mul p q => p.toPolynomial * q.toPolynomial

@[simp] theorem eval_toPolynomial (e : Expr σ) (v : σ → ℤ) :
    MvPolynomial.eval v e.toPolynomial = e.eval v := by
  induction e <;> simp_all [toPolynomial, eval]

end Expr

/-- Integer assignments obtained from natural input and witness coordinates. -/
def natAssignment {σ τ : Type*} (v : σ → ℕ) (w : τ → ℕ) : σ ⊕ τ → ℤ :=
  Sum.elim (fun i => (v i : ℤ)) (fun i => (w i : ℤ))

@[simp] theorem natAssignment_inl {σ τ : Type*} (v : σ → ℕ) (w : τ → ℕ) (i : σ) :
    natAssignment v w (.inl i) = v i := rfl
@[simp] theorem natAssignment_inr {σ τ : Type*} (v : σ → ℕ) (w : τ → ℕ) (i : τ) :
    natAssignment v w (.inr i) = w i := rfl

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

end NatExpr

namespace QuarticCompiler
open MvPolynomial

namespace Gates

variable {σ : Type*}

/-- A leaf has one node; an operation adds its root before its two subtrees. -/
abbrev Wire : NatExpr σ → Type
  | .constant _ => Fin 1
  | .var _ => Fin 1
  | .add p q => Fin 1 ⊕ (Wire p ⊕ Wire q)
  | .mul p q => Fin 1 ⊕ (Wire p ⊕ Wire q)

def count : NatExpr σ → ℕ
  | .constant _ => 1
  | .var _ => 1
  | .add p q => 1 + (count p + count q)
  | .mul p q => 1 + (count p + count q)

/-- The finite indexing is literal sum indexing, rather than `Fintype.equivFin`. -/
def index : (e : NatExpr σ) → Wire e ≃ Fin (count e)
  | .constant _ => Equiv.refl _
  | .var _ => Equiv.refl _
  | .add p q =>
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (Equiv.sumCongr (index p) (index q))).trans
        (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv)).trans finSumFinEquiv
  | .mul p q =>
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (Equiv.sumCongr (index p) (index q))).trans
        (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv)).trans finSumFinEquiv

instance (e : NatExpr σ) : Fintype (Wire e) := Fintype.ofEquiv (Fin (count e)) (index e).symm

/-- The output root of an expression tree. -/
def root : (e : NatExpr σ) → Wire e
  | .constant _ => 0
  | .var _ => 0
  | .add _ _ => Sum.inl 0
  | .mul _ _ => Sum.inl 0

/-- Actual acyclic gate code, expressed by one quadratic residual per node. -/
def residualSyntax : (e : NatExpr σ) → Wire e → Expr (σ ⊕ Wire e)
  | .constant n, _ => .var (Sum.inr 0) - .constant (n : ℤ)
  | .var i, _ => .var (Sum.inr 0) - .var (Sum.inl i)
  | .add p q, Sum.inl _ =>
      .var (Sum.inr (Sum.inl 0)) - (.var (Sum.inr (Sum.inr (Sum.inl (root p)))) + .var (Sum.inr (Sum.inr (Sum.inr (root q)))))
  | .add p _, Sum.inr (Sum.inl k) =>
      (residualSyntax p k).rename (Sum.map id (fun j => Sum.inr (Sum.inl j)))
  | .add _ q, Sum.inr (Sum.inr k) =>
      (residualSyntax q k).rename (Sum.map id (fun j => Sum.inr (Sum.inr j)))
  | .mul p q, Sum.inl _ =>
      .var (Sum.inr (Sum.inl 0)) - .var (Sum.inr (Sum.inr (Sum.inl (root p)))) * .var (Sum.inr (Sum.inr (Sum.inr (root q))))
  | .mul p _, Sum.inr (Sum.inl k) =>
      (residualSyntax p k).rename (Sum.map id (fun j => Sum.inr (Sum.inl j)))
  | .mul _ q, Sum.inr (Sum.inr k) =>
      (residualSyntax q k).rename (Sum.map id (fun j => Sum.inr (Sum.inr j)))

noncomputable def residual (e : NatExpr σ) (k : Wire e) : MvPolynomial (σ ⊕ Wire e) ℤ :=
  (residualSyntax e k).toPolynomial

/-- Canonical natural values at all syntax nodes. -/
def values : (e : NatExpr σ) → (σ → ℕ) → Wire e → ℕ
  | .constant n, _, _ => n
  | .var i, v, _ => v i
  | .add p q, v, Sum.inl _ => p.eval v + q.eval v
  | .add p _, v, Sum.inr (Sum.inl k) => values p v k
  | .add _ q, v, Sum.inr (Sum.inr k) => values q v k
  | .mul p q, v, Sum.inl _ => p.eval v * q.eval v
  | .mul p _, v, Sum.inr (Sum.inl k) => values p v k
  | .mul _ q, v, Sum.inr (Sum.inr k) => values q v k

@[simp] theorem values_root (e : NatExpr σ) (v : σ → ℕ) : values e v (root e) = e.eval v := by
  cases e <;> rfl

private theorem assignment_comp {τ ι : Type*} (v : σ → ℕ) (w : τ → ℕ) (f : ι → τ) :
    natAssignment v w ∘ Sum.map id f = natAssignment v (fun i => w (f i)) := by
  funext i
  cases i <;> rfl

/-- The explicit node evaluation satisfies every gate residual. -/
theorem complete (e : NatExpr σ) (v : σ → ℕ) :
    ∀ k : Wire e, (residualSyntax e k).eval (natAssignment v (values e v)) = 0 := by
  induction e with
  | constant n => intro k; simp [residualSyntax, Expr.eval, natAssignment, values]
  | var i => intro k; simp [residualSyntax, Expr.eval, natAssignment, values]
  | add p q hp hq =>
      intro k
      cases k with
      | inl j => simp [residualSyntax, Expr.eval, natAssignment, values, values_root]
      | inr k =>
          cases k with
          | inl k => simpa [residualSyntax, Expr.eval_rename, assignment_comp, values] using hp k
          | inr k => simpa [residualSyntax, Expr.eval_rename, assignment_comp, values] using hq k
  | mul p q hp hq =>
      intro k
      cases k with
      | inl j => simp [residualSyntax, Expr.eval, natAssignment, values, values_root]
      | inr k =>
          cases k with
          | inl k => simpa [residualSyntax, Expr.eval_rename, assignment_comp, values] using hp k
          | inr k => simpa [residualSyntax, Expr.eval_rename, assignment_comp, values] using hq k

#print axioms complete

end Gates
end QuarticCompiler
end DiophantineConsistency
