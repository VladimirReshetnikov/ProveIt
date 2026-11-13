import OrdinarySphere7084Literal

/-! Literal 69-row graph and its exact all-ring identity with the 70-row value. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OrdinarySphere6984Literal
open OrdinarySphere7084Literal
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

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
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  let qm := beta * J
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let X := w * q
  let Y := s * q3
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let ell := E * kY
  let c := kY + eta
  let a := E + Y
  let four_a := 4 * a
  let H := four_a + 3
  let a2 := a * a
  let Delta := a2 + H
  let ac := a * c
  let main_base := X + ac
  let gammaH := gamma * H
  let main_root := main_base + gammaH
  let c2 := c * c
  let Dc2 := Delta * c2
  let main_square := main_root * main_root
  let N1 := main_square - Dc2
  let qF := q - F
  let C := qF - alpha
  let gap_product := qm * qF
  let gap := gap_product + alpha
  let q2minus1 := q2 - 1
  let rproduct := gap * q2minus1
  let qMF := q * MF
  let maskfactor := MC + qMF
  let mask := maskfactor * J
  let R := rproduct + mask
  let En := E * n
  let tau_partial := En + k
  let tau := tau_partial - R
  let tau2 := tau * tau
  let ell_plus_k := ell + k
  let first_product := ell * ell_plus_k
  let N0 := tau2 - first_product
  let Kw := K0 + w
  let transport := Kw * C
  let transport_partial := transport + qF
  let zqm := z * qm
  let Nt := transport_partial - zqm
  let f2 := f * f
  let cT := c * T
  let cTminusR := cT - R
  let f2inner := f2 * cTminusR
  let V := f2inner - c
  let I := i * c2
  let I2 := I * I
  let f2m1 := f2 - 1
  let Aaux := Delta * f2m1
  let V2 := V * V
  let y2 := y * y
  let aux_gap := V2 - y2
  let aux_term := Aaux * aux_gap
  let Na := aux_term + y2
  let strong_residual := I2 - Aaux
  let Na2 := Na * Na
  let PQ := N0 * N1
  let PQW := PQ * Nt
  let PQWminus2 := PQW - 2
  let PQWproduct := PQW * PQWminus2
  let strong2 := strong_residual * strong_residual
  let sum1 := Na2 + strong2
  let polynomial := sum1 + PQWproduct
  polynomial

section Ring
variable {R : Type*} [CommRing R]
def value69 (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let d := Carrier65.core p v
  let I := d.i*d.c^2
  let strong := I^2-d.delta*(d.f^2-1)
  let X := d.P*d.Q*d.W
  (auxiliary d)^2 + strong^2 + X*(X-2)

theorem eval_expression (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt p).evalRing v = value69 (fun j => (p j : R)) v := by
  simp only [expressionAt, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    value69, auxiliary, Carrier65.core, pow_succ, pow_zero, one_mul]
  simp only [mul_assoc]

theorem tail_identity (u h x : R) : u^2+h^2+x*(x-2) = u^2+(x-1)^2+h^2-1 := by
  ring

theorem value_eq70 (p : Fin 4 → R) (v : Fin 14 → R) :
    value69 p v = OrdinarySphere7084Literal.value70 p v := by
  exact tail_identity _ _ _
end Ring

#print axioms eval_expression
#print axioms value_eq70
end DiophantineConsistency.OrdinarySphere6984Literal
