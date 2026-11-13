import DiophantineConsistency.Mixed121.Short15Graph

/-! # Package 54's 15-positive, 70-operation gate list of degree 80, at the 121x8801 ports

`54-calibrated-carry/positive/p70_degree80.json`: fifteen positive inputs
`J F α z f h i T s w τ η ζ y γ` and four fixed numerals `β K0 MC MF`. The output is
`A² + B(B − 2) + C²` with `A = N0·N1`, `B = Na·Nk·Nt` and `C = (ic²)² − Aaux`,
where (`Short15Graph`)

* `N0 = τ² − ℓ(ℓ + k)`, the first norm at the free root `τ`;
* `N1 = D² − Δc²`, `Nk = k − hE − R`, `Nt` the transport;
* `Na = Aaux(V² − y²) + y²` with `y` free and `V = f²(cT − R) − c`;
* `C = S`, the ordinary strong residual (`Ns` here, without the `+ 1`).

**Ports.** The fixed numerals are the leaves `.constant (p 0..3)`. Package 54
binds them to its own tuple `complemented-factorized-receiver-89x4831` (base
`2^429959`), which the tree does not calibrate; the endpoint
`IPRAPositive54p70` instantiates `p` at the wang943-mixed-121x8801 ports
`Mixed121Ports.ports` instead. So this is 54's gate list, not 54's literal
c54-port equation.

The gate block is generated from the pinned JSON by
`research/mixed121-calibration/tools/generate_short15_p54.py`, which also checks
it (`--check`). This module evaluates each gate group over an arbitrary
commutative ring. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P54p70Graph
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
  let tau : Expr (Fin 15) := .var 10
  let eta : Expr (Fin 15) := .var 11
  let zeta : Expr (Fin 15) := .var 12
  let y : Expr (Fin 15) := .var 13
  let gamma : Expr (Fin 15) := .var 14
  let beta : Expr (Fin 15) := .constant (p 0)
  let K0 : Expr (Fin 15) := .constant (p 1)
  let MC : Expr (Fin 15) := .constant (p 2)
  let MF : Expr (Fin 15) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
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
  let tau2 := tau * tau
  let ell_plus_k := ell + k
  let first_product := ell * ell_plus_k
  let N0 := tau2 - first_product
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
  let hE := h * E
  let index_partial := k - hE
  let Nk := index_partial - R
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
  let f2minus1 := f2 - 1
  let A0 := Delta * f2minus1
  let V2 := V * V
  let y2 := y * y
  let V2minusY2 := V2 - y2
  let aux_product := A0 * V2minusY2
  let Na := aux_product + y2
  let first_main := N0 * N1
  let aux_index := Na * Nk
  let aux_index_transport := aux_index * Nt
  let aux_minus_two := aux_index_transport - 2
  let strong_residual := I2 - A0
  let first_main2 := first_main * first_main
  let aux_falling_product := aux_index_transport * aux_minus_two
  let sum12 := first_main2 + aux_falling_product
  let strong_residual2 := strong_residual * strong_residual
  let polynomial := sum12 + strong_residual2
  -- END LITERAL GRAPH
  ⟨N0, N1, Na, Nk, Nt, strong_residual, polynomial⟩

section Ring
variable {R : Type*} [CommRing R]

theorem output_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).output.evalRing w =
      (graph p).N0.evalRing w * (graph p).N1.evalRing w *
          ((graph p).N0.evalRing w * (graph p).N1.evalRing w) +
        (graph p).Na.evalRing w * (graph p).Nk.evalRing w * (graph p).Nt.evalRing w *
          ((graph p).Na.evalRing w * (graph p).Nk.evalRing w * (graph p).Nt.evalRing w - 2) +
        (graph p).Ns.evalRing w * (graph p).Ns.evalRing w := by
  rw [show (graph p).output = (graph p).N0 * (graph p).N1 * ((graph p).N0 * (graph p).N1) +
      (graph p).Na * (graph p).Nk * (graph p).Nt * ((graph p).Na * (graph p).Nk * (graph p).Nt - 2) +
      (graph p).Ns * (graph p).Ns from rfl]
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_sub, Expr.evalRing_ofNat, Nat.cast_one,
    Nat.cast_ofNat]

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
    (graph p).N0.evalRing w = rN0 p w (w 10) := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Na_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).Na.evalRing w = rNa (vals p w).Aaux (vals p w).Vn (w 13) := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Ns_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).Ns.evalRing w = rS p w (w 6) := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

end Ring

end P54p70Graph

#print axioms P54p70Graph.output_eval
#print axioms P54p70Graph.N0_eval
#print axioms P54p70Graph.N1_eval
#print axioms P54p70Graph.Na_eval
#print axioms P54p70Graph.Nk_eval
#print axioms P54p70Graph.Nt_eval
#print axioms P54p70Graph.Ns_eval
