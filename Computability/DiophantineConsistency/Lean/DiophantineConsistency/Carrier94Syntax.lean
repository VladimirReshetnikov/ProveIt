import DiophantineConsistency.CurrentEquationSyntax2011

/-! # Literal syntax of the 14-positive 67/94 equation

Package 188 (`con-zfc-diophantine-forms/188-pell-orientation-exact-projection`,
`native/PROOF.md` §1, ordinary choice):

    Q94 = N0 * N1 * Na * Nt * Ns - 1,
    I = i c², Aaux = Delta (f² - 1),
    Na = Aaux (V² - y²) + y²,  Ns = 1 + I² - Aaux.

`expressionAt94` is written in the coordinate and port order of the maintained
`ObjectCurrentEquation2011.expressionAt`, with which it shares every register
except the auxiliary factor `U`, the strong factor `Z` and the final constant.
This module imports neither Foundation nor Mathlib's matrices. -/
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Carrier94Syntax
open ObjectCurrentEquation2011

def expressionAt94 (p : Fin 4 → ℤ) : Expr (Fin 14) :=
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
  let I := i * c ^ 2
  let Aaux := delta * (f ^ 2 - 1)
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let U := Aaux * (V ^ 2 - y ^ 2) + y ^ 2
  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b
  let Z := 1 + I ^ 2 - Aaux
  P * Q * U * W * Z - 1

/-- At the maintained current ports. -/
def expression94 : Expr (Fin 14) := expressionAt94 CurrentWindowCarry2011.ports

def naturalExpression94 : Expr (Fin 14) := positiveShift expression94

end DiophantineConsistency.Carrier94Syntax
