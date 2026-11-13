import DiophantineConsistency.WeightedExpressionDegree
import DiophantineConsistency.ModelCarrierScaled
/-! # Literal syntax of the scaled fourteen-variable carrier forms

The 67/106 and 66/118 expressions and their ring evaluations, in the
`ModelCarrierCurrent` namespace. This module imports neither Foundation nor
Mathlib's matrices (whose `Matrix.map` collides with Foundation's), so the
iPRA endpoints in `ModelCarrierCurrent` and the polynomial bindings in
`ModelCarrierBindings` can both name the same syntax. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelCarrierCurrent

/-! ### Literal syntax -/

/-- The 67/106 polynomial: the Carrier65 front with the normalized product. -/
def expressionAt106 (p : Fin 4 → ℤ) : Expr (Fin 14) :=
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
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b
  P * Q * (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2) * W *
    (f ^ 2 - delta * (i * c ^ 2) ^ 2) - 1

/-- The 66/118 polynomial: the Carrier65 front with the scaled auxiliary factor. -/
def expressionAt118 (p : Fin 4 → ℤ) : Expr (Fin 14) :=
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
  let W := (Expr.constant (p 1) + w) * C + (q - F) - z * b
  let Z := delta * f ^ 2 - S ^ 2
  P * Q * ((delta * f ^ 2 - delta) * (V ^ 2 - y ^ 2) + y ^ 2) * W * Z - delta

section Eval
variable {R : Type*} [CommRing R]

theorem evalRing_expressionAt106 (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt106 p).evalRing v = ModelCarrierScaled.value106 (fun j => (p j : R)) v := by
  simp only [expressionAt106, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    ModelCarrierScaled.value106, Carrier65.strong, Carrier65.core]

theorem evalRing_expressionAt118 (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt118 p).evalRing v = ModelCarrierScaled.value118 (fun j => (p j : R)) v := by
  simp only [expressionAt118, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    ModelCarrierScaled.value118, Carrier65.core]

end Eval

end DiophantineConsistency.ModelCarrierCurrent
