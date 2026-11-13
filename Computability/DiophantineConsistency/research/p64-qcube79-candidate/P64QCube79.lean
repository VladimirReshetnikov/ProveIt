import DiophantineConsistency.Compact44.P64Graph

/-! Generated q-cube first-root candidate.  No zero-equivalence is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace P64QCube79
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011

def graph (p : Fin 4 → ℤ) : P64Graph.Graph :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let t : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let e : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  -- BEGIN GENERATED GRAPH
  let q_minus_one := beta * J
  let q := q_minus_one + 1
  let q2 := q * q
  let q3 := q2 * q
  let Y := q3 * s
  let U := Y * Y
  let X := w * q
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let ell := E * kY
  let ell_plus_k := ell + k
  let first_product := ell * ell_plus_k
  let first_radicand := first_product + 1
  let first_unscaled_square := t * t
  let A0 := first_unscaled_square - first_radicand
  let c := kY + eta
  let a := E + Y
  let ac := a * c
  let b0 := X + ac
  let four_a := 4 * a
  let H := four_a + 3
  let a2 := a * a
  let Delta := a2 + H
  let c2 := c * c
  let Delta_c2 := Delta * c2
  let G := Delta_c2 + 1
  let q_minus_F := q - F
  let C := q_minus_F - alpha
  let gap_product := q_minus_one * q_minus_F
  let gap := gap_product + alpha
  let q2_minus_one := q2 - 1
  let R_product := gap * q2_minus_one
  let qMF := q * MF
  let mask_factor := MC + qMF
  let mask := mask_factor * J
  let R := R_product + mask
  let r_plus_one := k - R
  let r := r_plus_one - 1
  let U_gamma := U * gamma
  let main_gap := U_gamma - r
  let H_main_gap := H * main_gap
  let U_b0 := U * b0
  let Dstar := U_b0 + H_main_gap
  let Dstar2 := Dstar * Dstar
  let U2 := U * U
  let U2G := U2 * G
  let M := Dstar2 - U2G
  let Kplusw := K0 + w
  let transport_product := Kplusw * C
  let transport_sum := transport_product - F
  let transport_rhs := z * q_minus_one
  let Lt := transport_sum - transport_rhs
  let f2 := f * f
  let f2_minus_one := f2 - 1
  let cT := c * T
  let quotient_gap := cT - R
  let f2_quotient := f2 * quotient_gap
  let V := f2_quotient - c
  let y := V + e
  let V2 := V * V
  let y2 := y * y
  let square_gap := V2 - y2
  let I := i * c2
  let I2 := I * I
  let Aaux := Delta * f2_minus_one
  let W := I2 - Aaux
  let aux_term := Aaux * square_gap
  let Na := aux_term + y2
  let A0_square := A0 * A0
  let M_square := M * M
  let W_square := W * W
  let Na_square := Na * Na
  let Lt_square := Lt * Lt
  let sum0 := A0_square + M_square
  let sum1 := sum0 + W_square
  let sum2 := sum1 + Na_square
  let sum3 := sum2 + Lt_square
  let polynomial := sum3 - 1
  -- END GENERATED GRAPH
  ⟨A0, M, W, Na, Lt, polynomial⟩

end P64QCube79
