import DiophantineConsistency.Compact44.FreeJSumSquares
import Mathlib.Tactic.LinearCombination

/-! # Package 64's 14-positive, 83-operation equation of degree 30

`64-structural-reductions/positive14/polynomial.json`: fourteen positive inputs
`J F α z f i T Y w ρ η ζ e γ` and the four compact44 ports `β K0 MC MF`.
With `q = βJ + 1`, `X = wq`, `U = Y²` and `C = q − F − α`, the five residuals
are:

* `A0 = (q³(ℓ + ρ) + Y)² − q⁶(ℓ(ℓ+k) + 1)`, the first carrier;
* `M = D*² − U²(Δc² + 1)` with `D* = U(X + ac) + H(Uγ − (k − R − 1))`, the
  main carrier;
* `W = (ic²)² − Aaux` with `Aaux = Δ(f²−1)`, the ordinary strong norm;
* `Na = Aaux(V² − y²) + y²` with `V = f²(cT − R) − c` and `y = V + e`, the
  auxiliary norm;
* `Lt = (K0 + w)C − F − z(q−1)`, the transport.

The output is `A0² + M² + W² + Na² + Lt² − 1`. The gate block is generated
from the pinned JSON by `research/fourteen-p64-endpoint/tools/generate_p64.py`,
which also checks it. This module proves that a zero is a valuation where the
five squares sum to one and, for every residual, its evaluation in an
arbitrary commutative ring. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P64Graph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing

structure Graph where
  A0 : Expr (Fin 14)
  M : Expr (Fin 14)
  W : Expr (Fin 14)
  Na : Expr (Fin 14)
  Lt : Expr (Fin 14)
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
  let Y : Expr (Fin 14) := .var 7
  let w : Expr (Fin 14) := .var 8
  let rho : Expr (Fin 14) := .var 9
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
  let U := Y * Y
  let X := w * q
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let ell := E * kY
  let ell_plus_k := ell + k
  let first_product := ell * ell_plus_k
  let first_radicand := first_product + 1
  let ell_plus_rho := ell + rho
  let scaled_gap := q3 * ell_plus_rho
  let first_carrier := scaled_gap + Y
  let first_carrier_square := first_carrier * first_carrier
  let q6 := q3 * q3
  let scaled_first_radicand := q6 * first_radicand
  let A0 := first_carrier_square - scaled_first_radicand
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
  -- END LITERAL GRAPH
  ⟨A0, M, W, Na, Lt, polynomial⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).A0 * (graph p).A0 + (graph p).M * (graph p).M + (graph p).W * (graph p).W +
      (graph p).Na * (graph p).Na + (graph p).Lt * (graph p).Lt - 1 := by
  rfl

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero of the output is a valuation where the five squares sum to one. -/
theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    InternalZero (graph p).output v ↔
      let w : Fin 14 → DiffRing V := fun j => ι (v j)
      (graph p).A0.evalRing w * (graph p).A0.evalRing w + (graph p).M.evalRing w * (graph p).M.evalRing w +
        (graph p).W.evalRing w * (graph p).W.evalRing w + (graph p).Na.evalRing w * (graph p).Na.evalRing w +
        (graph p).Lt.evalRing w * (graph p).Lt.evalRing w = 1 := by
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
  q3 : R
  U : R
  X : R
  k : R
  ell : R
  c : R
  a : R
  H : R
  Delta : R
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
  let U := w 7 * w 7
  let X := w 8 * q
  let E := X * w 7
  let k := w 10 + w 11
  let kY := k * w 7
  let ell := E * kY
  let c := kY + w 10
  let a := E + w 7
  let H := 4 * a + 3
  let Delta := a * a + H
  let C := (q - w 1) - w 2
  let RR := (qm * (q - w 1) + w 2) * (q2 - 1) + ((p 2 : R) + q * (p 3 : R)) * w 0
  let Dstar := U * (X + a * c) + H * (U * w 13 - ((k - RR) - 1))
  let Aaux := Delta * (w 4 * w 4 - 1)
  let VV := (w 4 * w 4) * (c * w 6 - RR) - c
  let y := VV + w 12
  ⟨qm, q, q3, U, X, k, ell, c, a, H, Delta, C, RR, Dstar, Aaux, VV, y⟩

theorem A0_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).A0.evalRing w =
      ((vals p w).q3 * ((vals p w).ell + w 9) + w 7) * ((vals p w).q3 * ((vals p w).ell + w 9) + w 7) -
        ((vals p w).q3 * (vals p w).q3) * ((vals p w).ell * ((vals p w).ell + (vals p w).k) + 1) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

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

theorem Lt_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).Lt.evalRing w = (((p 1 : R) + w 8) * (vals p w).C - w 1) - w 3 * (vals p w).qm := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

end Ring

end P64Graph

#print axioms P64Graph.output_eq
#print axioms P64Graph.zero_iff
#print axioms P64Graph.A0_eval
#print axioms P64Graph.M_eval
#print axioms P64Graph.W_eval
#print axioms P64Graph.Na_eval
#print axioms P64Graph.Lt_eval
