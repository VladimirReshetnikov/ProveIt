import DiophantineConsistency.CantorRepresentation
import DiophantineConsistency.NaturalExpression

/-!
# Polynomial graph data without intermediate witnesses

A natural polynomial needs only its graph equation. A fixed positive
denominator may also be cleared, preserving the exact natural graph while
retaining explicit coefficient data.
-/

namespace DiophantineConsistency

namespace NatExpr

variable {σ : Type*}

/-- Interpret the supplied natural syntax as integer syntax, without any
ordinary polynomial coefficient operations. -/
def toInteger : NatExpr σ → Expr σ
  | .constant n => .constant (n : ℤ)
  | .var i => .var i
  | .add p q => p.toInteger + q.toInteger
  | .mul p q => p.toInteger * q.toInteger

theorem eval_toInteger (e : NatExpr σ) (v : σ → ℕ) :
    e.toInteger.eval (fun i => (v i : ℤ)) = (e.eval v : ℤ) := by
  induction e <;> simp_all [toInteger, eval]

/-- A polynomial graph needs zero extra witnesses, irrespective of its
degree. A later gate compiler may introduce its own quadratic wires. -/
def directGraphRep (e : NatExpr σ) : GraphRep e.eval :=
  (Rep.equality (Expr.var none) (e.toInteger.rename some)).ofIff (fun v => by
    simp only [Expr.eval_var, Expr.eval_rename]
    change (v none : ℤ) = e.toInteger.eval (fun i => (v (some i) : ℤ)) ↔ _
    rw [eval_toInteger, Int.natCast_inj]
    rfl)

theorem directGraphRep_witnessCount (e : NatExpr σ) : e.directGraphRep.witnessCount = 0 := rfl

end NatExpr

/-- Supplied natural polynomial data for a function after multiplication by
a fixed positive integer. No expression is selected from an existence proof. -/
structure ScaledNatural {σ : Type*} (f : (σ → ℕ) → ℕ) where
  denominator : ℕ
  positive : 0 < denominator
  numerator : NatExpr σ
  correct : ∀ v, numerator.eval v = denominator * f v

namespace ScaledNatural

variable {σ : Type*} {f g : (σ → ℕ) → ℕ}

def ofNatExpr (e : NatExpr σ) : ScaledNatural e.eval :=
  ⟨1, by decide, e, fun _ => (one_mul _).symm⟩

def constant (n : ℕ) : ScaledNatural (σ := σ) (fun _ => n) := ofNatExpr (.constant n)

def coordinate (i : σ) : ScaledNatural (fun v => v i) := ofNatExpr (.var i)

def add (p : ScaledNatural f) (q : ScaledNatural g) : ScaledNatural (fun v => f v + g v) :=
  { denominator := p.denominator * q.denominator
    positive := Nat.mul_pos p.positive q.positive
    numerator := p.numerator * .constant q.denominator + q.numerator * .constant p.denominator
    correct := fun v => by simp only [NatExpr.eval, p.correct, q.correct]; ring }

def mul (p : ScaledNatural f) (q : ScaledNatural g) : ScaledNatural (fun v => f v * g v) :=
  { denominator := p.denominator * q.denominator
    positive := Nat.mul_pos p.positive q.positive
    numerator := p.numerator * q.numerator
    correct := fun v => by simp only [NatExpr.eval, p.correct, q.correct]; ring }

/-- Clear the supplied fixed denominator in one exact graph equation. -/
def graphRep (p : ScaledNatural f) : GraphRep f :=
  (Rep.equality (.constant (p.denominator : ℤ) * .var none)
    (p.numerator.toInteger.rename some)).ofIff (fun v => by
      simp only [Expr.eval_mul, Expr.eval_constant, Expr.eval_var, Expr.eval_rename]
      change (p.denominator : ℤ) * (v none : ℤ) =
        p.numerator.toInteger.eval (fun i => (v (some i) : ℤ)) ↔ _
      rw [NatExpr.eval_toInteger, ← Int.natCast_mul, Int.natCast_inj, p.correct]
      exact ⟨fun h => Nat.eq_of_mul_eq_mul_left p.positive h,
        fun h => congrArg (fun n => p.denominator * n) h⟩)

theorem graphRep_witnessCount (p : ScaledNatural f) : p.graphRep.witnessCount = 0 := rfl

/-- A nested Cantor pairing still has a fixed-denominator natural polynomial
graph. Clearing that denominator adds no existential witness. -/
def cantorPair (p : ScaledNatural f) (q : ScaledNatural g) :
    ScaledNatural (fun v => SetTheory.BusyBeaver.ZFC.Code254.P (f v) (g v)) := by
  let d := p.denominator * q.denominator
  let a := p.numerator * NatExpr.constant q.denominator
  let b := q.numerator * NatExpr.constant p.denominator
  let s := a + b
  refine
    { denominator := 2 * d ^ 2
      positive := Nat.mul_pos (by decide) (pow_pos (Nat.mul_pos p.positive q.positive) 2)
      numerator := s * (s + .constant d) + .constant 2 * b * .constant d
      correct := ?_ }
  intro v
  have hs : s.eval v = d * (f v + g v) := by
    dsimp only [s, a, b, NatExpr.eval]
    rw [p.correct, q.correct]
    dsimp only [d]
    ring
  have hb : b.eval v = d * g v := by
    dsimp only [b, NatExpr.eval]
    rw [q.correct]
    dsimp only [d]
    ring
  simp only [NatExpr.eval, hs, hb]
  calc
    _ = d ^ 2 * ((f v + g v) * (f v + g v + 1) + 2 * g v) := by ring
    _ = d ^ 2 * (2 * SetTheory.BusyBeaver.ZFC.Code254.P (f v) (g v)) := by
      rw [CantorRepresentation.two_pair]
    _ = _ := by ring

end ScaledNatural
end DiophantineConsistency
