import Std

/-!
# Kerr--Newman: explicit finite rational syntax and proof targets

STATUS: uncompiled Lean 4 outline. No theorem below claims that the complete
Kerr--Newman calculation has already been checked by Lean. The definitions are
complete; the remaining mathematical assertions are named proposition-valued
targets, not axioms. The final theorem is explicitly conditional on those targets.

Variables are [m,a,q,r,x]. Coordinate indices are [t,r,x,phi].
Signature is (-,+,+,+). We use R_ij = d_k Gamma^k_ij - d_j Gamma^k_ik
  + Gamma^k_ij Gamma^l_kl - Gamma^l_ik Gamma^k_jl.

The deliberately unreduced normalizer is a transparent reference specification.
A practical replay should consume the factored polynomial certificates in code/;
its extra factor-cancellation steps require their own checked multiplication laws.
-/

namespace KNIPRA

abbrev V := Fin 5
abbrev I := Fin 4

inductive Expr where
  | const : Int → Expr
  | var : V → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
  | inv : Expr → Expr
  deriving DecidableEq, Repr

namespace Expr

def pow (e : Expr) : Nat → Expr
  | 0 => .const 1
  | n + 1 => .mul (pow e n) e

instance (n : Nat) : OfNat Expr n := ⟨.const (Int.ofNat n)⟩
instance : Add Expr := ⟨.add⟩
instance : Mul Expr := ⟨.mul⟩
instance : Neg Expr := ⟨.neg⟩
instance : Sub Expr := ⟨fun e f => .add e (.neg f)⟩
instance : Div Expr := ⟨fun e f => .mul e (.inv f)⟩
instance : HPow Expr Nat Expr := ⟨pow⟩

def eval (rho : V → Rat) : Expr → Rat
  | .const z => (z : Rat)
  | .var v => rho v
  | .add e f => eval rho e + eval rho f
  | .mul e f => eval rho e * eval rho f
  | .neg e => -eval rho e
  | .inv e => 1 / eval rho e

/-- The actual domain guard of the rational-expression tree. -/
def safe (rho : V → Rat) : Expr → Prop
  | .const _ => True
  | .var _ => True
  | .add e f => safe rho e ∧ safe rho f
  | .mul e f => safe rho e ∧ safe rho f
  | .neg e => safe rho e
  | .inv e => safe rho e ∧ eval rho e ≠ 0

/-- Formal partial derivative, with all five indeterminates available. -/
def diff (v : V) : Expr → Expr
  | .const _ => 0
  | .var w => if v = w then 1 else 0
  | .add e f => diff v e + diff v f
  | .mul e f => diff v e * f + e * diff v f
  | .neg e => -(diff v e)
  | .inv e => -(diff v e / (e ^ 2))

end Expr

open Expr

/-- Raw polynomial terms; duplicates and zero coefficients are allowed. -/
structure Term where
  coefficient : Int
  exponent : Vector Nat 5
  deriving DecidableEq, Repr

abbrev Poly := List Term

namespace Poly

def constant (z : Int) : Poly :=
  [{ coefficient := z, exponent := Vector.replicate 5 0 }]

def variable (v : V) : Poly :=
  [{ coefficient := 1,
     exponent := Vector.ofFn (fun w => if v = w then 1 else 0) }]

def add (p q : Poly) : Poly := p ++ q

def neg (p : Poly) : Poly := p.map (fun t => {t with coefficient := -t.coefficient})

def mul (p q : Poly) : Poly :=
  p.flatMap (fun t => q.map (fun u => {
    coefficient := t.coefficient * u.coefficient,
    exponent := Vector.ofFn (fun v => t.exponent[v] + u.exponent[v]) }))

def coefficientAt (p : Poly) (e : Vector Nat 5) : Int :=
  (p.map (fun t => if t.exponent = e then t.coefficient else 0)).foldl (· + ·) 0

/-- It suffices to inspect supports that occur in the finite term list. -/
def isZero (p : Poly) : Bool :=
  p.all (fun t => decide (coefficientAt p t.exponent = 0))

def termValue (rho : V → Rat) (t : Term) : Rat :=
  (t.coefficient : Rat) *
    ((List.finRange 5).map (fun v => rho v ^ t.exponent[v])).foldl (· * ·) 1

def eval (rho : V → Rat) (p : Poly) : Rat :=
  (p.map (termValue rho)).foldl (· + ·) 0

end Poly

/-- Numerator and denominator, using only explicit integer-polynomial arithmetic.
There is no gcd, factorization oracle, or semantic equality decision here. -/
def normalize : Expr → Poly × Poly
  | .const z => (Poly.constant z, Poly.constant 1)
  | .var v => (Poly.variable v, Poly.constant 1)
  | .neg e => let p := normalize e; (Poly.neg p.1, p.2)
  | .add e f =>
      let p := normalize e
      let q := normalize f
      (Poly.add (Poly.mul p.1 q.2) (Poly.mul q.1 p.2), Poly.mul p.2 q.2)
  | .mul e f =>
      let p := normalize e
      let q := normalize f
      (Poly.mul p.1 q.1, Poly.mul p.2 q.2)
  | .inv e => let p := normalize e; (p.2, p.1)

def m : Expr := .var 0
def a : Expr := .var 1
def q : Expr := .var 2
def r : Expr := .var 3
def x : Expr := .var 4
def U : Expr := 1 - x ^ 2
def S : Expr := r ^ 2 + a ^ 2 * x ^ 2
def D : Expr := r ^ 2 - 2 * m * r + a ^ 2 + q ^ 2
def B : Expr := r ^ 2 + a ^ 2

def dd (i : I) (e : Expr) : Expr :=
  if i.val = 1 then e.diff 3 else if i.val = 2 then e.diff 4 else 0

def sum4 (f : I → Expr) : Expr :=
  ((List.finRange 4).map f).foldl (· + ·) 0

abbrev Matrix := I → I → Expr

def metric (i j : I) : Expr :=
  match i.val, j.val with
  | 0, 0 => -(D - a ^ 2 * U) / S
  | 0, 3 => -a * U * (B - D) / S
  | 3, 0 => -a * U * (B - D) / S
  | 1, 1 => S / D
  | 2, 2 => S / U
  | 3, 3 => U * (B ^ 2 - a ^ 2 * D * U) / S
  | _, _ => 0

def inverseMetric (i j : I) : Expr :=
  match i.val, j.val with
  | 0, 0 => -(B ^ 2 - a ^ 2 * D * U) / (S * D)
  | 0, 3 => -a * (B - D) / (S * D)
  | 3, 0 => -a * (B - D) / (S * D)
  | 1, 1 => D / S
  | 2, 2 => U / S
  | 3, 3 => (D - a ^ 2 * U) / (S * D * U)
  | _, _ => 0

def potential (i : I) : Expr :=
  match i.val with
  | 0 => -q * r / S
  | 3 => q * r * a * U / S
  | _ => 0

def field (i j : I) : Expr := dd i (potential j) - dd j (potential i)

def raisedField (i j : I) : Expr :=
  sum4 (fun k => sum4 (fun l => inverseMetric i k * inverseMetric j l * field k l))

def gamma (i j k : I) : Expr :=
  (1 / 2) * sum4 (fun l => inverseMetric i l *
    (dd j (metric l k) + dd k (metric l j) - dd l (metric j k)))

def ricci (i j : I) : Expr :=
  sum4 (fun k => dd k (gamma k i j) - dd j (gamma k i k) +
    sum4 (fun l => gamma k i j * gamma l k l - gamma l i k * gamma k j l))

def fieldSquare : Expr :=
  sum4 (fun i => sum4 (fun j => field i j * raisedField i j))

def emRHS (i j : I) : Expr :=
  2 * (sum4 (fun k => sum4 (fun l =>
    field i k * inverseMetric k l * field j l)) - metric i j * fieldSquare / 4)

def einsteinResidual (i j : I) : Expr := ricci i j - emRHS i j

def maxwellResidual (j : I) : Expr :=
  sum4 (fun i => dd i (S * raisedField i j))

def bianchiResidual (i j k : I) : Expr :=
  dd i (field j k) + dd j (field k i) + dd k (field i j)

def inverseResidual (i j : I) : Expr :=
  sum4 (fun k => metric i k * inverseMetric k j) - (if i = j then 1 else 0)

def residuals : List Expr :=
  (List.finRange 4).flatMap (fun i => (List.finRange 4).map (einsteinResidual i)) ++
  (List.finRange 4).map maxwellResidual ++
  (List.finRange 4).flatMap (fun i => (List.finRange 4).flatMap
    (fun j => (List.finRange 4).map (bianchiResidual i j))) ++
  (List.finRange 4).flatMap (fun i => (List.finRange 4).map (inverseResidual i))

def check : Bool := residuals.all (fun e => Poly.isZero (normalize e).1)

def Regular (rho : V → Rat) : Prop :=
  S.eval rho ≠ 0 ∧ D.eval rho ≠ 0 ∧ U.eval rho ≠ 0

def ArithmeticGoal : Prop :=
  ∀ rho, Regular rho → ∀ e ∈ residuals, e.eval rho = 0

/-! These goals expose all bridges needed before claiming ArithmeticGoal.
The paper proves their mathematical content with fixed finite arithmetic;
their Lean implementation remains to be completed. -/

def CoefficientSoundGoal : Prop :=
  ∀ (p : Poly) (rho : V → Rat), Poly.isZero p = true → Poly.eval rho p = 0

def NormalizationSoundGoal : Prop :=
  ∀ (e : Expr) (rho : V → Rat), e.safe rho →
    Poly.eval rho (normalize e).2 ≠ 0 ∧
    e.eval rho = Poly.eval rho (normalize e).1 / Poly.eval rho (normalize e).2

def GuardPropagationGoal : Prop :=
  ∀ rho, Regular rho → ∀ e ∈ residuals, e.safe rho

def CheckedResidualsGoal : Prop :=
  ∀ e ∈ residuals, Poly.isZero (normalize e).1 = true

/-- This is a conditional assembly theorem, not the discharged main result. -/
theorem arithmetic_of_obligations
    (hCoeff : CoefficientSoundGoal) (hNorm : NormalizationSoundGoal)
    (hGuard : GuardPropagationGoal) (hCheck : CheckedResidualsGoal) : ArithmeticGoal := by
  intro rho hr e he
  have hn := (hNorm e rho (hGuard rho hr e he)).2
  have hz := hCoeff (normalize e).1 rho (hCheck e he)
  rw [hn, hz]
  simp [Rat.div_def]

end KNIPRA
