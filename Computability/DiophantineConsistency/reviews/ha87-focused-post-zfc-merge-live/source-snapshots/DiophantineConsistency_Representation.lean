import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Fin.Basic

/-!
# Executable syntax for finite Diophantine representations

`Expr` stores arithmetic syntax, and `Rep` stores a finite witness count and
an expression together with its correctness theorem. Both live in `Type`:
their data are supplied directly, rather than extracted from a proposition
using choice. The expression evaluator and all representation constructors
are executable. `Expr.toPolynomial` supplies the ordinary mathematical
polynomial denoted by the same syntax.
-/

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

/-- Renaming inputs and witnesses commutes with the natural assignment. -/
theorem natAssignment_comp_map {σ σ' τ τ' : Type*}
    (v : σ' → ℕ) (w : τ' → ℕ) (f : σ → σ') (g : τ → τ') :
    natAssignment v w ∘ Sum.map f g = natAssignment (v ∘ f) (w ∘ g) := by
  funext i
  cases i <;> rfl

/-- A representation is data: a finite witness count and an explicit expression.
The theorem field certifies the expression supplied by the constructor. -/
structure Rep (σ : Type*) (P : (σ → ℕ) → Prop) where
  witnessCount : ℕ
  expression : Expr (σ ⊕ Fin witnessCount)
  correct : ∀ v, P v ↔ ∃ w : Fin witnessCount → ℕ,
    expression.eval (natAssignment v w) = 0

namespace Rep

variable {σ τ : Type*} {P Q : (σ → ℕ) → Prop}

/-- Change the predicate while preserving all representation data. -/
def ofIff (r : Rep σ P) (h : ∀ v, P v ↔ Q v) : Rep σ Q where
  witnessCount := r.witnessCount
  expression := r.expression
  correct v := (h v).symm.trans (r.correct v)

/-- The supplied expression also represents the predicate as an ordinary
multivariate polynomial with integer coefficients. -/
theorem correct_toPolynomial (r : Rep σ P) (v : σ → ℕ) :
    P v ↔ ∃ w : Fin r.witnessCount → ℕ,
      MvPolynomial.eval (natAssignment v w) r.expression.toPolynomial = 0 := by
  simpa only [Expr.eval_toPolynomial] using r.correct v

/-- An arithmetic equality needs no witnesses. -/
def equality (p q : Expr σ) :
    Rep σ (fun v => p.eval (fun i => (v i : ℤ)) = q.eval (fun i => (v i : ℤ))) where
  witnessCount := 0
  expression := (p - q).rename Sum.inl
  correct v := by
    simp only [Expr.eval_rename, Expr.eval_sub]
    constructor
    · intro h
      exact ⟨Fin.elim0, sub_eq_zero.mpr h⟩
    · rintro ⟨w, hw⟩
      exact sub_eq_zero.mp hw

/-- Precompose the predicate with a map of input coordinates. -/
def reindex (r : Rep σ P) (f : σ → τ) : Rep τ (fun v => P (v ∘ f)) where
  witnessCount := r.witnessCount
  expression := r.expression.rename (Sum.map f id)
  correct v := by
    simpa only [Expr.eval_rename, natAssignment_comp_map, Function.comp_id] using
      r.correct (v ∘ f)

/-- Conjunction combines independent witness blocks and adds the squares of
the two residuals. No decisions about the represented predicates are made. -/
def conjunction (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∧ Q v) := by
  let left := r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount))
  let right := s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))
  refine ⟨r.witnessCount + s.witnessCount, left * left + right * right, ?_⟩
  intro v
  simp only [left, right, Expr.eval_add, Expr.eval_mul, Expr.eval_rename,
    natAssignment_comp_map, Function.comp_id, mul_self_add_mul_self_eq_zero]
  rw [r.correct, s.correct]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨Fin.addCases a b, ?_, ?_⟩
    · simpa [Function.comp_def] using ha
    · simpa [Function.comp_def] using hb
  · rintro ⟨w, ha, hb⟩
    exact ⟨⟨w ∘ Fin.castAdd s.witnessCount, ha⟩,
      ⟨w ∘ Fin.natAdd r.witnessCount, hb⟩⟩

/-- Disjunction multiplies residuals and keeps independent witness blocks.
The unused branch may take all its natural witnesses to be zero. -/
def disjunction (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∨ Q v) := by
  let left := r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount))
  let right := s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))
  refine ⟨r.witnessCount + s.witnessCount, left * right, ?_⟩
  intro v
  simp only [left, right, Expr.eval_mul, Expr.eval_rename,
    natAssignment_comp_map, Function.comp_id, mul_eq_zero]
  rw [r.correct, s.correct]
  constructor
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · refine ⟨Fin.addCases a (fun _ => 0), Or.inl ?_⟩
      simpa [Function.comp_def] using ha
    · refine ⟨Fin.addCases (fun _ => 0) b, Or.inr ?_⟩
      simpa [Function.comp_def] using hb
  · rintro ⟨w, ha | hb⟩
    · exact Or.inl ⟨w ∘ Fin.castAdd s.witnessCount, ha⟩
    · exact Or.inr ⟨w ∘ Fin.natAdd r.witnessCount, hb⟩

/-- Move a finite block of input coordinates into the existential witnesses. -/
def existsBlock {k : ℕ} {P : (σ ⊕ Fin k → ℕ) → Prop}
    (r : Rep (σ ⊕ Fin k) P) : Rep σ (fun v => ∃ a : Fin k → ℕ, P (Sum.elim v a)) := by
  let index : (σ ⊕ Fin k) ⊕ Fin r.witnessCount → σ ⊕ Fin (k + r.witnessCount)
    | .inl (.inl i) => .inl i
    | .inl (.inr i) => .inr (Fin.castAdd r.witnessCount i)
    | .inr i => .inr (Fin.natAdd k i)
  refine ⟨k + r.witnessCount, r.expression.rename index, ?_⟩
  intro v
  have heval (w : Fin (k + r.witnessCount) → ℕ) :
      (r.expression.rename index).eval (natAssignment v w) =
        r.expression.eval (natAssignment (Sum.elim v (w ∘ Fin.castAdd r.witnessCount))
          (w ∘ Fin.natAdd k)) := by
    rw [Expr.eval_rename]
    apply congrArg r.expression.eval
    funext i
    rcases i with (i | i) | i <;> rfl
  simp only [heval]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := (r.correct _).mp ha
    exact ⟨Fin.addCases a b, by simpa [Function.comp_def] using hb⟩
  · rintro ⟨w, hw⟩
    exact ⟨w ∘ Fin.castAdd r.witnessCount, (r.correct _).mpr ⟨w ∘ Fin.natAdd k, hw⟩⟩

end Rep

end DiophantineConsistency
