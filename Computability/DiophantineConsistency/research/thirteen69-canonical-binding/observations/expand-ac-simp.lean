import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ThirteenCarrier

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Thirteen69Expression
open DiophantineConsistency
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ModelDifferenceRing
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=
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
  let beta : Expr (Fin 13) := .constant (p 0)
  let K0 : Expr (Fin 13) := .constant (p 1)
  let MC : Expr (Fin 13) := .constant (p 2)
  let MF : Expr (Fin 13) := .constant (p 3)
  -- BEGIN GRAPH
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
  let B := transport - F
  let f2 := f * f
  let cT := c * T
  let cTminusR := cT - R
  let f2inner := f2 * cTminusR
  let V := f2inner - c
  let hi := qm * i
  let normalized_S := hi * Dc2
  let normalized_S2 := normalized_S * normalized_S
  let V2 := V * V
  let LB := V2 * B
  let mLB := m - LB
  let h_mLB := qm * mLB
  let carrier := h_mLB - B
  let four_carrier := 4 * carrier
  let y := four_carrier + 1
  let y2 := y * y
  let V2minusY2 := V2 - y2
  let aux_product := normalized_S2 * V2minusY2
  let Na := aux_product + y2
  let scaled_f2 := Delta * f2
  let scaled_Ns := scaled_f2 - normalized_S2
  let product0 := N0 * N1
  let product1 := product0 * Na
  let product4 := product1 * scaled_Ns
  let polynomial := product4 - Delta
  -- END GRAPH
  polynomial

theorem eval_literal {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (literal p).evalRing v = ThirteenCarrier.value69 (fun j => (p j : R)) v := by
  simp only [literal, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Nat.cast_ofNat, Nat.cast_one, ThirteenCarrier.value69, ThirteenCarrier.core,
    pow_succ, pow_zero, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc,
    add_comm, add_left_comm, add_assoc]

end Thirteen69Expression
#print axioms Thirteen69Expression.eval_literal
