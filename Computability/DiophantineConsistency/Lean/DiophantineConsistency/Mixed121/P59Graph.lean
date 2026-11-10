import DiophantineConsistency.Mixed121.P55Graph

/-! # Package 59's 14-positive, 79-operation equation of degree 52

`59-degree-separated/short/circuits/p79_d52_14positive.json`: fourteen positive
inputs `J F α z f i T s w τ η ζ u γ` and the four wang943-mixed-121x8801 ports
`β K0 MC MF` (the package's `COEFFICIENT_BINDING.json` pins exactly package 55's
four payload hashes). Its residuals are package 55's (`P55Graph`), with one gate
block rearranged:

* `M`, `W`, `N0` and `Nt` evaluate exactly as package 55's;
* `Na = ŷ² − Aaux·u·(V + ŷ)` with `ŷ = V + u`, which equals package 55's
  `Aaux(V² − y²) + y²` at `y = ŷ`, since `u(V + ŷ) = ŷ² − V²`.

The output is `M² + (Na − 1)² + (N0·Nt − 1)² + W²`, not package 55's
`M² + W² + Na² + (N0·Nt − 1)² − 1`. This module proves, over an arbitrary
commutative ring, that each residual evaluates as package 55's and that the
output is that sum of four squares. The gate block is generated from the pinned
JSON by `research/mixed121-calibration/tools/generate_p59.py`, which also checks
it. Nothing here depends on the ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P59Graph
open DiophantineConsistency
open AdaptiveEquationSyntax2011

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : P55Graph.Graph :=
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
  let u : Expr (Fin 14) := .var 12
  let gamma : Expr (Fin 14) := .var 13
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let q1 := beta * J
  let q := q1 + 1
  let q2 := q * q
  let q3 := q2 * q
  let X := w * q
  let Y := s * q3
  let E := X * Y
  let k := eta + zeta
  let kY := k * Y
  let L := E * kY
  let Lplusk := L + k
  let first_term := L * Lplusk
  let tau2 := tau * tau
  let N0 := tau2 - first_term
  let c := kY + eta
  let a := E + Y
  let ac := a * c
  let b0 := X + ac
  let foura := 4 * a
  let H := foura + 3
  let a2 := a * a
  let Delta := a2 + H
  let c2 := c * c
  let Dc2 := Delta * c2
  let qF := q - F
  let C := qF - alpha
  let Gpart := q1 * qF
  let G := Gpart + alpha
  let q2m1 := q2 - 1
  let Rpart := G * q2m1
  let qMF := q * MF
  let Mpart := MC + qMF
  let mask := Mpart * J
  let R := Rpart + mask
  let q4 := q2 * q2
  let U := 4 * q4
  let main_target := Dc2 + 1
  let k_R := k - R
  let index_gap := k_R - 1
  let Ugamma := U * gamma
  let carrier := Ugamma - index_gap
  let Hcarrier := H * carrier
  let Ub0 := U * b0
  let Dstar := Ub0 + Hcarrier
  let Dstar2 := Dstar * Dstar
  let U2 := U * U
  let U2target := U2 * main_target
  let main_residual := Dstar2 - U2target
  let Kw := K0 + w
  let KwC := Kw * C
  let transport_partial := KwC + qF
  let zq1 := z * q1
  let Nt := transport_partial - zq1
  let f2 := f * f
  let cT := c * T
  let cT_R := cT - R
  let f2inner := f2 * cT_R
  let V := f2inner - c
  let I := i * c2
  let I2 := I * I
  let f2m1 := f2 - 1
  let Aaux := Delta * f2m1
  let yhat := V + u
  let yhat2 := yhat * yhat
  let V_yhat := V + yhat
  let gap_product := u * V_yhat
  let aux_term := Aaux * gap_product
  let Na := yhat2 - aux_term
  let res0 := Na - 1
  let group1_0 := N0 * Nt
  let res1 := group1_0 - 1
  let strong_residual := I2 - Aaux
  let sq0 := main_residual * main_residual
  let sq1 := res0 * res0
  let sq2 := res1 * res1
  let sq3 := strong_residual * strong_residual
  let sum0 := sq0 + sq1
  let sum1 := sum0 + sq2
  let polynomial := sum1 + sq3
  -- END LITERAL GRAPH
  ⟨main_residual, strong_residual, Na, N0, Nt, polynomial⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).M * (graph p).M + ((graph p).Na - 1) * ((graph p).Na - 1) +
      ((graph p).N0 * (graph p).Nt - 1) * ((graph p).N0 * (graph p).Nt - 1) +
      (graph p).W * (graph p).W := by
  rfl

section Ring
variable {R : Type*} [CommRing R]
open P55Graph (vals)

theorem output_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).output.evalRing w =
      (graph p).M.evalRing w * (graph p).M.evalRing w +
        ((graph p).Na.evalRing w - 1) * ((graph p).Na.evalRing w - 1) +
        ((graph p).N0.evalRing w * (graph p).Nt.evalRing w - 1) *
          ((graph p).N0.evalRing w * (graph p).Nt.evalRing w - 1) +
        (graph p).W.evalRing w * (graph p).W.evalRing w := by
  rw [output_eq]
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_sub, Expr.evalRing_ofNat,
    Nat.cast_one]

theorem M_eq (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).M.evalRing w = (P55Graph.graph p).M.evalRing w := by
  rw [P55Graph.M_eval]
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem W_eq (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).W.evalRing w = (P55Graph.graph p).W.evalRing w := by
  rw [P55Graph.W_eval]
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem N0_eq (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).N0.evalRing w = (P55Graph.graph p).N0.evalRing w := by
  rw [P55Graph.N0_eval]
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Nt_eq (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).Nt.evalRing w = (P55Graph.graph p).Nt.evalRing w := by
  rw [P55Graph.Nt_eval]
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

/-- The rearranged auxiliary norm, in package 55's registers. -/
theorem Na_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).Na.evalRing w =
      (vals p w).y * (vals p w).y -
        (vals p w).Aaux * (w 12 * ((vals p w).V + (vals p w).y)) := by
  simp only [graph, vals, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Na_eq (p : Fin 4 → ℤ) (w : Fin 14 → R) :
    (graph p).Na.evalRing w = (P55Graph.graph p).Na.evalRing w := by
  rw [Na_eval, P55Graph.Na_eval]
  have hy : (vals p w).y = (vals p w).V + w 12 := rfl
  rw [hy]
  ring

end Ring

end P59Graph

#print axioms P59Graph.output_eval
#print axioms P59Graph.M_eq
#print axioms P59Graph.Na_eq
