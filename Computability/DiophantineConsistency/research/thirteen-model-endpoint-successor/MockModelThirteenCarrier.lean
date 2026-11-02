import DiophantineConsistency.Thirteen69Nodes
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
open AdaptiveEquationSyntax2011
/-- The common thirteen-coordinate front, followed by `final P Q S f δ gap y t`. -/
def front13 (p : Fin 4 → ℤ)
    (final : Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) →
      Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13)) :
    Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let f : Expr (Fin 13) := .var 3
  let i : Expr (Fin 13) := .var 4
  let T : Expr (Fin 13) := .var 5
  let s : Expr (Fin 13) := .var 6
  let w : Expr (Fin 13) := .var 7
  let n : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let m : Expr (Fin 13) := .var 11
  let gamma : Expr (Fin 13) := .var 12
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
  let G := (Expr.constant (p 1) + w) * C - F
  let y := 1 + 4 * (b * (m - V ^ 2 * G) - G)
  final (tau ^ 2 - ell * (ell + k)) (D ^ 2 - delta * c ^ 2) (delta * (b * i * c ^ 2))
    f delta (V ^ 2 - y ^ 2) y (b * i * c ^ 2)

/-- The 13/69/174 polynomial. -/
def expressionAt69 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13 p fun P Q S f delta gap y _ =>
    P * Q * (S ^ 2 * gap + y ^ 2) * (delta * f ^ 2 - S ^ 2) - delta

theorem evalRing_expressionAt69 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt69 p).evalRing v = ThirteenCarrier.value69 (fun j => (p j : R)) v := by
  simp only [expressionAt69, front13, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    ThirteenCarrier.value69, ThirteenCarrier.core]


end DiophantineConsistency.ModelThirteenCarrier
