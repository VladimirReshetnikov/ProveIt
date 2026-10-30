import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.ArithmeticExpression

/-! The maintained literal expression and HA sentence, with their original names.
Only definition ownership changes; wide native and object semantics remain separate. -/
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ObjectCurrentEquation2011

/-- Literal arithmetic syntax, in the same coordinate and port order as
`Carrier65.core`. All four ports are single integer-constant leaves. -/
def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let n : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let y : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let b := Expr.constant (p 0) * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) +
    (Expr.constant (p 2) + q * Expr.constant (p 3)) * J
  let tau := E * n + k - rank
  let V := f ^ 2 * (c * T - rank) - c
  let S := i * delta * c ^ 2
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let U := S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2
  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b
  let Z := delta * f ^ 2 - S ^ 2
  P * Q * U * W * Z - delta

/-- The current ports retain the full kernel and both complete masks. -/
def expression : Expr (Fin 14) := expressionAt CurrentWindowCarry2011.ports

/-- This substitution changes the domain, without adding any variables. -/
def positiveShift {σ : Type*} (e : Expr σ) : Expr σ :=
  e.subst (fun i => Expr.var i + Expr.constant 1)

def naturalExpression : Expr (Fin 14) := positiveShift expression

/-- The generic pair identity prevents any expansion of the large current
split-natural tree. It holds over every commutative semiring. -/
theorem split_positiveShift {σ R : Type*} [CommSemiring R]
    (e : Expr σ) (v : σ → R) :
    ((positiveShift e).splitNatural.1.evalSemiring v,
      (positiveShift e).splitNatural.2.evalSemiring v) =
      (e.splitNatural.1.evalSemiring (fun i => v i + 1),
       e.splitNatural.2.evalSemiring (fun i => v i + 1)) := by
  induction e <;>
    simp_all [positiveShift, Expr.subst, Expr.splitNatural, NatExpr.evalSemiring]

def InternalZero {σ R : Type*} [CommSemiring R] (e : Expr σ) (v : σ → R) : Prop :=
  e.splitNatural.1.evalSemiring v = e.splitNatural.2.evalSemiring v

theorem internalZero_positiveShift {σ R : Type*} [CommSemiring R]
    (e : Expr σ) (v : σ → R) :
    InternalZero (positiveShift e) v ↔ InternalZero e (fun i => v i + 1) :=
  Iff.of_eq (congrArg (fun p : R × R => p.1 = p.2) (split_positiveShift e v))

end DiophantineConsistency.ObjectCurrentEquation2011

namespace DiophantineConsistency.ArithmeticCurrentEquation2011
open SetTheory.PA ObjectCurrentEquation2011

/-- A literal closed formula in the ordinary `0,S,+,*` language. -/
def unsolvabilitySentence : Formula :=
  ArithmeticExpression.noZeroSentence naturalExpression

end DiophantineConsistency.ArithmeticCurrentEquation2011
