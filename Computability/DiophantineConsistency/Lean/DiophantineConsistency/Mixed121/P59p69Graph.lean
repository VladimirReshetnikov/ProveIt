import DiophantineConsistency.Mixed121.Short15Graph

/-! # Package 59's 15-positive, 69-operation equation of degree 91

`59-degree-separated/short/circuits/p69_d91.json`: fifteen positive inputs
`J F α z f h i T s w r η ζ y γ` and the four wang943-mixed-121x8801 ports
`β K0 MC MF`. The output is `N0·N1·Na·Nk·Nt·Ns − 1`, where (`Short15Graph`)

* `N0 = r² + ℓ(2r − k) = (ℓ + r)² − ℓ(ℓ + k)`, the first norm with a gap;
* `N1 = D² − Δc²`, `Nk = k − hE − R`, `Nt` the transport;
* `Na = Aaux(V² − y²) + y²` with `y` free and `V = f²(cT − R) − c`;
* `Ns = (ic²)² − Aaux + 1`.

The gate block is generated from the pinned JSON by
`research/mixed121-calibration/tools/generate_short15.py`, which also checks it
(`--check`). This module evaluates each gate group over an arbitrary
commutative ring. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P59p69Graph
open DiophantineConsistency AdaptiveEquationSyntax2011 Short15Graph

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Short15Graph.Graph :=
  let J : Expr (Fin 15) := .var 0
  let F : Expr (Fin 15) := .var 1
  let alpha : Expr (Fin 15) := .var 2
  let z : Expr (Fin 15) := .var 3
  let f : Expr (Fin 15) := .var 4
  let h : Expr (Fin 15) := .var 5
  let i : Expr (Fin 15) := .var 6
  let T : Expr (Fin 15) := .var 7
  let s : Expr (Fin 15) := .var 8
  let w : Expr (Fin 15) := .var 9
  let r : Expr (Fin 15) := .var 10
  let eta : Expr (Fin 15) := .var 11
  let zeta : Expr (Fin 15) := .var 12
  let y : Expr (Fin 15) := .var 13
  let gamma : Expr (Fin 15) := .var 14
  let beta : Expr (Fin 15) := .constant (p 0)
  let K0 : Expr (Fin 15) := .constant (p 1)
  let MC : Expr (Fin 15) := .constant (p 2)
  let MF : Expr (Fin 15) := .constant (p 3)
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
  let r2 := r * r
  let twice_r := 2 * r
  let first_gap := twice_r - k
  let first_term := L * first_gap
  let N0 := r2 + first_term
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
  let gammaH := gamma * H
  let D := b0 + gammaH
  let D2 := D * D
  let N1 := D2 - Dc2
  let hE := h * E
  let k_hE := k - hE
  let Nk := k_hE - R
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
  let V2 := V * V
  let y2 := y * y
  let aux_gap := V2 - y2
  let aux_term := Aaux * aux_gap
  let Na := aux_term + y2
  let strong_residual := I2 - Aaux
  let Ns := strong_residual + 1
  let prod0 := N0 * N1
  let prod1 := prod0 * Na
  let prod2 := prod1 * Nk
  let prod3 := prod2 * Nt
  let prod4 := prod3 * Ns
  let polynomial := prod4 - 1
  -- END LITERAL GRAPH
  ⟨N0, N1, Na, Nk, Nt, Ns, polynomial⟩

section Ring
variable {R : Type*} [CommRing R]

theorem output_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).output.evalRing w =
      (graph p).N0.evalRing w * (graph p).N1.evalRing w * (graph p).Na.evalRing w * (graph p).Nk.evalRing w *
        (graph p).Nt.evalRing w * (graph p).Ns.evalRing w - 1 := by
  rw [show (graph p).output = (graph p).N0 * (graph p).N1 * (graph p).Na * (graph p).Nk *
      (graph p).Nt * (graph p).Ns - 1 from rfl]
  simp only [Expr.evalRing_mul, Expr.evalRing_sub, Expr.evalRing_ofNat, Nat.cast_one]

theorem N1_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).N1.evalRing w = rN1 p w := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Nk_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).Nk.evalRing w = rNk p w := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Nt_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).Nt.evalRing w = rNt p w := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem N0_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).N0.evalRing w = rN0 p w ((vals p w).ell + w 10) := by
  rw [← first_gap]
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Na_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).Na.evalRing w = rNa (vals p w).Aaux (vals p w).Vn (w 13) := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Ns_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).Ns.evalRing w = rS p w (w 6) + 1 := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

end Ring

end P59p69Graph

#print axioms P59p69Graph.output_eval
#print axioms P59p69Graph.N0_eval
#print axioms P59p69Graph.N1_eval
#print axioms P59p69Graph.Na_eval
#print axioms P59p69Graph.Nk_eval
#print axioms P59p69Graph.Nt_eval
#print axioms P59p69Graph.Ns_eval
