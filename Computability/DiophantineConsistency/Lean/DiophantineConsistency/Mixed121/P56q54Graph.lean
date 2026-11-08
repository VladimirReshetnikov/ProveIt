import DiophantineConsistency.Mixed121.Short15Graph

/-! # Package 56's 15-positive, 73-operation equation of degree 54

`56-free-coordinate/short/generated/ordinary_gap_minima73_squared_modulus_degree54.json`:
fifteen positive inputs `J F α z f h i T s w τ η ζ e γ` and the four
wang943-mixed-121x8801 ports (package 31's `coefficients31` payloads). The output
is `N0² + Na² + (N1·(Nk·Nt) − 1)² + S² − 2`, where `N0`, `N1`, `Nk`, `Nt`, `S`
are as in `Short15Graph` and the auxiliary gap norm
`Na = (V + e)² − Aaux·e(V + (V + e))` is `Aaux(V² − y²) + y²` at `y = V + e`.
The gate block is generated and checked by
`research/mixed121-calibration/tools/generate_short15.py`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P56q54Graph
open DiophantineConsistency AdaptiveEquationSyntax2011 Short15Graph

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Short15Graph.Graph :=
  let Jrep : Expr (Fin 15) := .var 0
  let F : Expr (Fin 15) := .var 1
  let alpha : Expr (Fin 15) := .var 2
  let transport_quotient : Expr (Fin 15) := .var 3
  let f : Expr (Fin 15) := .var 4
  let h : Expr (Fin 15) := .var 5
  let i : Expr (Fin 15) := .var 6
  let auxiliary_quotient : Expr (Fin 15) := .var 7
  let s : Expr (Fin 15) := .var 8
  let w : Expr (Fin 15) := .var 9
  let tau_root : Expr (Fin 15) := .var 10
  let eta : Expr (Fin 15) := .var 11
  let zeta : Expr (Fin 15) := .var 12
  let auxiliary_gap : Expr (Fin 15) := .var 13
  let gamma : Expr (Fin 15) := .var 14
  let Bm1 : Expr (Fin 15) := .constant (p 0)
  let Kconstant : Expr (Fin 15) := .constant (p 1)
  let MC : Expr (Fin 15) := .constant (p 2)
  let MF : Expr (Fin 15) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let tau_square := tau_root * tau_root
  let repunit := Bm1 * Jrep
  let q := repunit + 1
  let Lbig := q * q
  let n2 := Lbig * q
  let wn2 := w * q
  let sn2 := s * n2
  let UM := wn2 * sn2
  let R10b := eta + zeta
  let ksn2 := R10b * sn2
  let first_root_base := UM * ksn2
  let first_next := first_root_base + R10b
  let first_product := first_root_base * first_next
  let norm_first := tau_square - first_product
  let R10a := ksn2 + eta
  let R12 := UM + sn2
  let cam2 := R10a * R12
  let D1 := wn2 + cam2
  let a4 := 4 * R12
  let a4m5 := a4 + 3
  let gam := gamma * a4m5
  let R14 := D1 + gam
  let L15 := R14 * R14
  let a_square := R12 * R12
  let A := a_square + a4m5
  let c2 := R10a * R10a
  let Ac2 := A * c2
  let norm_main := L15 - Ac2
  let q_minus_F := q - F
  let C := q_minus_F - alpha
  let hpm1 := h * UM
  let index_difference := R10b - hpm1
  let gap_product := repunit * q_minus_F
  let gap := gap_product + alpha
  let Lm1 := Lbig - 1
  let rproduct := gap * Lm1
  let qMF := q * MF
  let mask_factor := MC + qMF
  let mask := mask_factor * Jrep
  let r_lhs := rproduct + mask
  let norm_index := index_difference - r_lhs
  let kinner := Kconstant + w
  let innerC := kinner * C
  let local_rhs := transport_quotient * repunit
  let transport_partial := innerC + q_minus_F
  let norm_transport := transport_partial - local_rhs
  let L16 := f * f
  let auxiliary_cT := R10a * auxiliary_quotient
  let auxiliary_inner := auxiliary_cT - r_lhs
  let auxiliary_scaled := L16 * auxiliary_inner
  let aux_u_rhs := auxiliary_scaled - R10a
  let f2_minus_one := L16 - 1
  let R16 := A * f2_minus_one
  let ordinary_ic2 := i * c2
  let ordinary_ic2_square := ordinary_ic2 * ordinary_ic2
  let gap_y := aux_u_rhs + auxiliary_gap
  let aux_y2 := gap_y * gap_y
  let twice_V_gap := aux_u_rhs + gap_y
  let gap_product_aux := auxiliary_gap * twice_V_gap
  let L17 := R16 * gap_product_aux
  let norm_aux := aux_y2 - L17
  let index_transport := norm_index * norm_transport
  let main_index_transport := norm_main * index_transport
  let unit_error := main_index_transport - 1
  let strong_error := ordinary_ic2_square - R16
  let norm_first_sq := norm_first * norm_first
  let norm_aux_sq := norm_aux * norm_aux
  let unit_error_sq := unit_error * unit_error
  let strong_error_sq := strong_error * strong_error
  let total2 := norm_first_sq + norm_aux_sq
  let total3 := total2 + unit_error_sq
  let total4 := total3 + strong_error_sq
  let polynomial := total4 - 2
  -- END LITERAL GRAPH
  ⟨norm_first, norm_main, norm_aux, norm_index, norm_transport, strong_error, polynomial⟩

section Ring
variable {R : Type*} [CommRing R]

theorem output_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).output.evalRing w =
      (graph p).N0.evalRing w * (graph p).N0.evalRing w + (graph p).Na.evalRing w * (graph p).Na.evalRing w +
        ((graph p).N1.evalRing w * ((graph p).Nk.evalRing w * (graph p).Nt.evalRing w) - 1) *
          ((graph p).N1.evalRing w * ((graph p).Nk.evalRing w * (graph p).Nt.evalRing w) - 1) +
        (graph p).Ns.evalRing w * (graph p).Ns.evalRing w - 2 := by
  rw [show (graph p).output = (graph p).N0 * (graph p).N0 + (graph p).Na * (graph p).Na +
      ((graph p).N1 * ((graph p).Nk * (graph p).Nt) - 1) * ((graph p).N1 * ((graph p).Nk * (graph p).Nt) - 1) +
      (graph p).Ns * (graph p).Ns - 2 from rfl]
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_sub, Expr.evalRing_ofNat, Nat.cast_one,
    Nat.cast_ofNat]

theorem N1_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).N1.evalRing w = rN1 p w := by
  have h : (graph p).N1.evalRing w =
      ((vals p w).X + (vals p w).c * (vals p w).a + w 14 * (vals p w).H) *
        ((vals p w).X + (vals p w).c * (vals p w).a + w 14 * (vals p w).H) -
        (vals p w).Delta * ((vals p w).c * (vals p w).c) := by
    simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
      Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
      Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]
  have hD : (vals p w).D = (vals p w).X + (vals p w).a * (vals p w).c + w 14 * (vals p w).H := rfl
  rw [h, rN1, hD]; ring

theorem Nk_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).Nk.evalRing w = rNk p w := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Nt_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).Nt.evalRing w = rNt p w := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem N0_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).N0.evalRing w = rN0 p w (w 10) := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Na_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) :
    (graph p).Na.evalRing w = rNa (vals p w).Aaux (vals p w).Vn ((vals p w).Vn + w 13) := by
  rw [← aux_gap]
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

theorem Ns_eval (p : Fin 4 → ℤ) (w : Fin 15 → R) : (graph p).Ns.evalRing w = rS p w (w 6) := by
  simp only [graph, vals, rN0, rN1, rNk, rNt, rS, rNa, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Int.cast_one,
    Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat]

end Ring

end P56q54Graph

#print axioms P56q54Graph.output_eval
#print axioms P56q54Graph.N0_eval
#print axioms P56q54Graph.N1_eval
#print axioms P56q54Graph.Na_eval
#print axioms P56q54Graph.Nk_eval
#print axioms P56q54Graph.Nt_eval
#print axioms P56q54Graph.Ns_eval
