import DiophantineConsistency.Compact44.FreeJSumSquares
import Mathlib.Tactic.LinearCombination

/-! # Package 55's 14-positive, 79-operation equation of degree 52

`55-congruence-norms/fourteen/polynomial.json`: fourteen positive inputs
`J F α z f i T s w τ η ζ e γ` and the four wang943-mixed-121x8801 ports
`β K0 MC MF`. With `q = βJ + 1`, `X = wq`, `Y = sq³`, `U = 4q⁴` and
`C = q − F − α`, the residuals are:

* `M = D*² − U²(Δc² + 1)` with `D* = U(X + ac) + H(Uγ − (k − R − 1))`, the
  main carrier;
* `W = (ic²)² − Aaux` with `Aaux = Δ(f²−1)`, the ordinary strong norm;
* `Na = Aaux(V² − y²) + y²` with `V = f²(cT − R) − c` and `y = V + e`, the
  auxiliary norm;
* `N0 = τ² − ℓ(ℓ + k)`, the first norm;
* `Nt = (K0 + w)C + (q − F) − z(q−1)`, the transport.

The output is `M² + W² + Na² + (N0·Nt − 1)² − 1`. The gate block is generated
from the pinned JSON by `research/mixed121-calibration/tools/generate_p55.py`,
which also checks it. This module proves that a zero is a valuation where the
four squares sum to one and, for every residual, its evaluation in an
arbitrary commutative ring. Nothing here depends on the ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P55Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing

structure Graph where
  M : Expr (Fin 14)
  W : Expr (Fin 14)
  Na : Expr (Fin 14)
  N0 : Expr (Fin 14)
  Nt : Expr (Fin 14)
  output : Expr (Fin 14)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let J : Expr (Fin 14) := .var 0
  let F : Expr (Fin 14) := .var 1
  let alpha : Expr (Fin 14) := .var 2
  let z : Expr (Fin 14) := .var 3
  let f : Expr (Fin 14) := .var 4
  let i : Expr (Fin 14) := .var 5
  let T : Expr (Fin 14) := .var 6
  let s : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let tau : Expr (Fin 14) := .var 9
  let eta : Expr (Fin 14) := .var 10
  let zeta : Expr (Fin 14) := .var 11
  let e : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let q_minus_one := beta * J
  let q := q_minus_one + 1
  let q2 := q * q
  let q3 := q2 * q
  let q4 := q2 * q2
  let U := 4 * q4
  let X := w * q
  let Y := s * q3
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let ell := E * kY
  let ell_plus_k := ell + k
  let first_part := ell * ell_plus_k
  let tau2 := tau * tau
  let N0 := tau2 - first_part
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
  let carrier := U_gamma - r
  let H_carrier := H * carrier
  let U_b0 := U * b0
  let Dstar := U_b0 + H_carrier
  let Dstar2 := Dstar * Dstar
  let U2 := U * U
  let U2G := U2 * G
  let main_residual := Dstar2 - U2G
  let Kplusw := K0 + w
  let transport_product := Kplusw * C
  let transport_sum := transport_product + q_minus_F
  let transport_rhs := z * q_minus_one
  let Nt := transport_sum - transport_rhs
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
  let strong_residual := I2 - Aaux
  let aux_term := Aaux * square_gap
  let Na := aux_term + y2
  let first_transport := N0 * Nt
  let first_transport_residual := first_transport - 1
  let main_residual_square := main_residual * main_residual
  let strong_residual_square := strong_residual * strong_residual
  let Na_square := Na * Na
  let first_transport_residual_square := first_transport_residual * first_transport_residual
  let sum0 := main_residual_square + strong_residual_square
  let sum1 := sum0 + Na_square
  let sum2 := sum1 + first_transport_residual_square
  let polynomial := sum2 - 1
  -- END LITERAL GRAPH
  ⟨main_residual, strong_residual, Na, N0, Nt, polynomial⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).M * (graph p).M + (graph p).W * (graph p).W + (graph p).Na * (graph p).Na +
      ((graph p).N0 * (graph p).Nt - 1) * ((graph p).N0 * (graph p).Nt - 1) - 1 := by
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero of the output is a valuation where the four squares sum to one. -/
theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    InternalZero (graph p).output v ↔
      let w : Fin 14 → DiffRing V := fun j => ι (v j)
      (graph p).M.evalRing w * (graph p).M.evalRing w + (graph p).W.evalRing w * (graph p).W.evalRing w +
        (graph p).Na.evalRing w * (graph p).Na.evalRing w +
        ((graph p).N0.evalRing w * (graph p).Nt.evalRing w - 1) *
          ((graph p).N0.evalRing w * (graph p).Nt.evalRing w - 1) = 1 := by
  rw [output_eq, internalZero_iff]
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_sub, Expr.evalRing_ofNat, Nat.cast_one]
  exact sub_eq_zero

/-! ## Ring evaluation of the residuals -/

section Ring
variable {R : Type*} [CommRing R]

/-- Named register values, gate by gate. -/
structure Vals (R : Type*) where
  qm : R
  q : R
  U : R
  X : R
  Y : R
  k : R
  ell : R
  c : R
  a : R
  H : R
  Delta : R
  qF : R
  C : R
  RR : R
  Dstar : R
  Aaux : R
  V : R
  y : R

def vals (p : Fin 4 → ℤ) (w : Fin 14 → R) : Vals R :=
  let qm := (p 0 : R) * w 0
  let q := qm + 1
  let q2 := q * q
  let q3 := q2 * q
  let q4 := q2 * q2
  let U := 4 * q4
  let X := w 8 * q
  let Y := w 7 * q3
  let E := X * Y
  let k := w 10 + w 11
  let kY := k * Y
  let ell := E * kY
  let c := kY + w 10
  let a := E + Y
  let H := 4 * a + 3
  let Delta := a * a + H
  let qF := q - w 1
  let C := qF - w 2
  let RR := (qm * qF + w 2) * (q2 - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0
  let Dstar := U * (X + a * c) + H * (U * w 13 - ((k - RR) - 1))
  let Aaux := Delta * (w 4 * w 4 - 1)
  let VV := (w 4 * w 4) * (c * w 6 - RR) - c
  let y := VV + w 12
  ⟨qm, q, U, X, Y, k, ell, c, a, H, Delta, qF, C, RR, Dstar, Aaux, VV, y⟩

theorem M_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).M.evalRing w =
      (vals p w).Dstar * (vals p w).Dstar - ((vals p w).U * (vals p w).U) *
        ((vals p w).Delta * ((vals p w).c * (vals p w).c) + 1) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem W_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).W.evalRing w =
      (w 5 * ((vals p w).c * (vals p w).c)) * (w 5 * ((vals p w).c * (vals p w).c)) - (vals p w).Aaux := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Na_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).Na.evalRing w =
      (vals p w).Aaux * ((vals p w).V * (vals p w).V - (vals p w).y * (vals p w).y) +
        (vals p w).y * (vals p w).y := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem N0_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).N0.evalRing w = w 9 * w 9 - (vals p w).ell * ((vals p w).ell + (vals p w).k) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Nt_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).Nt.evalRing w =
      (((p 1 : R) + w 8) * (vals p w).C + (vals p w).qF) - w 3 * (vals p w).qm := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

end Ring

end P55Graph

#print axioms P55Graph.output_eq
#print axioms P55Graph.zero_iff
#print axioms P55Graph.M_eval
#print axioms P55Graph.W_eval
#print axioms P55Graph.Na_eval
#print axioms P55Graph.N0_eval
#print axioms P55Graph.Nt_eval
