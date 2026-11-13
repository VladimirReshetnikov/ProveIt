import DiophantineConsistency.JonesSyntaxCore
import DiophantineConsistency.QuarticSyntaxCore
import DiophantineConsistency.SyntaxCoefficients
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Matrix-free data of the executable Jones syntax

The definitions of `ExecutableJones`, with their original names, moved out
of that module so that model-internal (Foundation) modules can name the
nine-variable syntax: the proofs import Mathlib's matrices, whose
`Matrix.map` collides with Foundation's. `codingStar`, `codingExpo`,
`codingLexp` and `codingL4` are verbatim copies of `Jones1982.star`,
`expo`, `Lexp` and `L4`; `ExecutableJones` proves each copy equal to its
original by `rfl`. -/

namespace DiophantineConsistency.ExecutableJones

open NinePolynomial

/-- Copy of `Jones1982.star`: exponent vectors with `Σ k = δ`. -/
def codingStar (ν δ : ℕ) : Finset (Fin (ν + 2) → ℕ) :=
  (Finset.univ : Finset (Fin (ν + 2))).piAntidiag δ

/-- Copy of `Jones1982.expo`. -/
def codingExpo (ν δ : ℕ) (k : Fin (ν + 2) → ℕ) : ℕ :=
  ∑ j : Fin (ν + 1), k j.succ * (δ + 1) ^ (j : ℕ)

/-- Copy of `Jones1982.Lexp`. -/
abbrev codingLexp (ν δ : ℕ) : ℕ := (δ + 1) ^ (ν + 1)

/-- Copy of `Jones1982.L4`. -/
abbrev codingL4 (ν : ℕ) : ℕ := codingLexp ν 4

/-- Sum over a literal finite range; only syntax construction is involved. -/
def rangeSum {σ : Type*} (n : ℕ) (f : Fin n → Expr σ) : Expr σ :=
  QuarticSyntax.sumExpressions (List.ofFn f)

/-- Explicit nested enumeration of all bounded exponent vectors. -/
def vectorSum {σ : Type*} : (n : ℕ) → ((Fin n → Fin 5) → Expr σ) → Expr σ
  | 0, f => f Fin.elim0
  | n + 1, f => rangeSum 5 fun a => vectorSum n fun b => f (Fin.cons a b)

/-- Sum over the star with an explicit, executable order of its vectors. -/
def starSum {σ : Type*} (ν : ℕ) (f : (Fin (ν + 2) → ℕ) → Expr σ) : Expr σ :=
  vectorSum (ν + 2) fun k =>
    if (∑ j, (k j : ℕ)) = 4 then f (fun j => (k j : ℕ)) else .constant 0

/-- The Jones coefficient, computed directly from the supplied syntax. -/
def pCoefficient {ν : ℕ} (e : Expr (Fin (ν + 1))) (k : Fin (ν + 2) → ℕ) : ℤ :=
  ((∏ j, (k j).factorial : ℕ) : ℤ) *
    SyntaxCoefficients.coefficient (SyntaxCoefficients.expand e) (fun j => k j.succ)

def indexExponent {ν : ℕ} (e : Expr (Fin (ν + 1))) (bound : ℕ) : ℕ :=
  bound + (∑ k ∈ codingStar ν 4, (pCoefficient e k).natAbs) + 2

def indexZ {ν : ℕ} (e : Expr (Fin (ν + 1))) (bound : ℕ) : ℕ :=
  2 ^ indexExponent e bound

def indexY {ν : ℕ} (e : Expr (Fin (ν + 1))) (bound : ℕ) : ℕ :=
  (∑ k ∈ codingStar ν 4,
    ((indexZ e bound : ℤ) + pCoefficient e k) *
      (2 * indexZ e bound : ℤ) ^ (codingLexp ν 4 - codingExpo ν 4 k)).toNat

/-- The coefficient encoding polynomial emitted by its literal star sum. -/
def eExpression {σ : Type*} {ν : ℕ} (e : Expr (Fin (ν + 1))) (z : ℕ) (B : Expr σ) :
    Expr σ :=
  starSum ν fun k =>
    .constant ((z : ℤ) + pCoefficient e k) * B ^ (codingLexp ν 4 - codingExpo ν 4 k)

/-- The fixed coding polynomial `l` emitted as a prefix sum. -/
def lExpression {σ : Type*} (B : Expr σ) : ℕ → Expr σ
  | 0 => .constant 0
  | n + 1 => lExpression B n + B ^ (5 ^ (n + 1))

/-- The geometric coding polynomial `λ` emitted as a literal range sum. -/
def lamExpression {σ : Type*} (ν : ℕ) (B : Expr σ) : Expr σ :=
  rangeSum (4 * codingLexp ν 4) fun i => B ^ (i : ℕ)

/-- Every free Jones quantity, using only executable syntax constructors. -/
def syntaxVars {ν : ℕ} (seed : Expr (Fin (ν + 1))) (z y : ℕ) :
    RingVars (Expr (Fin 10)) :=
  let x : Expr (Fin 10) := .var 0
  let b := x * .constant (y : ℤ) + 1 + .var 1
  let q := (b ^ 5) ^ codingL4 ν
  let n := q ^ 16
  let e := eExpression seed z (b ^ 5)
  let l := lExpression (b ^ 5) ν
  let lam := lamExpression ν (b ^ 5)
  let g : Expr (Fin 10) := .var 2 + 1
  let θ := b ^ 5 - 2 * .constant (z : ℤ)
  ⟨rankCode x (.constant (z : ℤ)) b e g l n q θ lam,
    n, b, g, 32 * b * (b ^ 5) ^ (5 ^ ν),
    .var 3 + 1, .var 4 + 1, .var 5 + 1, .var 6, .var 7 + 1, .var 8 + 1⟩

def withInput {ν : ℕ} (seed : Expr (Fin (ν + 1))) (z y : ℕ) : Expr (Fin 10) :=
  let v := syntaxVars seed z y
  RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) (.var 9)
    v.dvsr v.dvnd v.marg

/-- Executable nine-unknown syntax from a supplied seed expression. -/
def expression {ν : ℕ} (seed : Expr (Fin (ν + 1))) (bound : ℕ := 0) : Expr (Fin 9) :=
  JonesSyntax.removeInput (withInput seed (indexZ seed bound) (indexY seed bound))

end DiophantineConsistency.ExecutableJones
