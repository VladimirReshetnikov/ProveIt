import DiophantineConsistency.P138.P138Squares
import DiophantineConsistency.BFS943.AdjacentInteger

/-! # The adjacent-Pell descent makes the auxiliary ordinate integral

`PROOF.md`, "Soundness": "The adjacent-Pell descent from the retained parent proof makes
`y = e/delta` integral." With `c ≠ 0`, `U ≠ 0` and `BP ≥ 1`, so `Q = Delta² U² BP > 1` and
`delta = Q − 1 > 0` (`Q_gt`); then `Da = delta · Cy = e² > 0` gives `Cy > 0` and `V ≠ 0`.
The scaled norm `(1 + delta)(delta |V|)² = delta² + delta · e²` is exactly `e² = delta (Q V² − 1)`,
so `TenPositiveAdjacentInteger.quotient_of_scaled_norm` (with `B = M = delta`, `v = |V|`, `z = e`)
gives `e = delta · y` and `Q V² − (Q − 1) y² = 1` (`aux_integral`). This is the same use as
`TenPositive80Adjacent.graph_adjacent`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Adjacent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot P138Squares

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓡" => regs p x

theorem ι_pos {a : V} (h : 0 < a) : (0 : DiffRing V) < ι a := by
  rw [← map_zero ι]; exact ι_lt_ι.mpr h

/-- At a zero with `c ≠ 0`, `U ≠ 0`. -/
theorem U_ne (hp : PortFacts p) (hz : value p x = 0) (hc : x 8 ≠ 0) : (𝓡).U ≠ 0 := by
  have hA := abs_A p x hp
  have hA0 : (𝓡).A ≠ 0 := by intro h0; rw [h0, abs_zero] at hA; linarith
  rw [U_eq]
  exact mul_ne_zero (mul_ne_zero hA0 (s_r_ne p x hp hz).2) (pow_ne_zero 2 hc)

/-- At a zero, `BP ≥ 1`. -/
theorem BP_ge (hp : PortFacts p) (hz : value p x = 0) : 1 ≤ (𝓡).BP := by
  obtain ⟨p0, _, _, hp0, _, _, hBP, _, _⟩ := roots p x hp hz
  have h1 : (1 : DiffRing V) ≤ ι p0 := by rw [← map_one ι]; exact ι_le_ι.mpr (pos_iff_one_le.mp hp0)
  rw [hBP]; nlinarith

/-- **`Q > 1`** at a zero with `c ≠ 0`. -/
theorem Q_gt (hp : PortFacts p) (hz : value p x = 0) (hc : x 8 ≠ 0) : 1 < (𝓡).Q := by
  have hU1 : 1 ≤ (𝓡).U ^ 2 := by
    have := one_le_abs (U_ne p x hp hz hc); rw [← sq_abs]; nlinarith
  have hD := Delta_gt p x hp
  have hBP := BP_ge p x hp hz
  have hD2 : 64 ≤ (𝓡).Delta ^ 2 := by nlinarith
  have h1 : 64 ≤ (𝓡).Delta ^ 2 * (𝓡).U ^ 2 := by nlinarith
  rw [Q_eq]; nlinarith

/-- **The auxiliary ordinate is integral.** -/
theorem aux_integral (hp : PortFacts p) (hz : value p x = 0) (hc : x 8 ≠ 0) {e : V}
    (he : Da p x = ι e * ι e) (he0 : 0 < e) :
    ∃ y : V, 0 < y ∧ ι e = ((𝓡).Q - 1) * ι y ∧
      (𝓡).Q * (𝓡).V ^ 2 - ((𝓡).Q - 1) * (ι y) ^ 2 = 1 := by
  have hQ := Q_gt p x hp hz hc
  obtain ⟨dn, hdn⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ (𝓡).Q - 1 by linarith)
  have hdn0 : 0 < dn := by
    rcases eq_zero_or_pos dn with h0 | h0
    · rw [h0, map_zero] at hdn; linarith
    · exact h0
  have hCy : 0 < (𝓡).Q * (𝓡).V ^ 2 - 1 := by
    have hDa : 0 < Da p x := by rw [he]; exact mul_pos (ι_pos he0) (ι_pos he0)
    unfold Da at hDa
    exact pos_of_mul_pos_right hDa (by linarith)
  have hV : (𝓡).V ≠ 0 := by
    intro h0; rw [h0] at hCy; linarith [show (𝓡).Q * (0 : DiffRing V) ^ 2 - 1 = -1 by ring]
  obtain ⟨vn, hvn⟩ := abs_eq_ι (𝓡).V
  have hvn0 : 0 < vn := by
    rcases eq_zero_or_pos vn with h0 | h0
    · rw [h0, map_zero] at hvn; exact absurd (abs_eq_zero.mp hvn) hV
    · exact h0
  have hVV : |(𝓡).V| * |(𝓡).V| = (𝓡).V ^ 2 := by rw [abs_mul_abs_self]; ring
  have hscaled : (1 + dn) * ((dn * vn) * (dn * vn)) = dn * dn + dn * (e * e) := by
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    rw [← hdn, ← hvn, ← he]
    unfold Da
    linear_combination ((𝓡).Q * ((𝓡).Q - 1) ^ 2) * hVV
  obtain ⟨y, hy, hnorm⟩ :=
    TenPositiveAdjacentInteger.quotient_of_scaled_norm dn dn vn e hdn0 hdn0 hvn0 hscaled
  have hy0 : 0 < y := by
    rcases eq_zero_or_pos y with h0 | h0
    · rw [h0, mul_zero] at hy; exact absurd hy he0.ne'
    · exact h0
  refine ⟨y, hy0, by rw [hy, map_mul, hdn], ?_⟩
  have h := congrArg (ι (V := V)) hnorm
  simp only [map_add, map_mul, map_one] at h
  rw [← hdn, ← hvn, hVV] at h
  linear_combination h

end Regs

#print axioms U_ne
#print axioms BP_ge
#print axioms Q_gt
#print axioms aux_integral

end DiophantineConsistency.P138Adjacent
