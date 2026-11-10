import DiophantineConsistency.LinCof.LCBudget
import DiophantineConsistency.P138.P138Adjacent

/-! # The adjacent-Pell descent makes the auxiliary ordinate integral

At a zero of the linear-cofactor output, `LCSquares.budget_ge` gives a positive budget, so
`c ≠ 0` and `Delta ≥ 8` (`LCBudget`), and `B = u² ≥ 1` (`LCSquares.roots`). Hence
`Q = Delta² c⁴ B > 1` (`Q_gt`) and `delta = Q − 1 > 0`; then `Da = delta · Cy = e² > 0` gives
`Cy > 0` and `V ≠ 0`. The scaled norm `(1 + delta)(delta |V|)² = delta² + delta · e²` is exactly
`e² = delta (Q V² − 1)`, so `TenPositiveAdjacentInteger.quotient_of_scaled_norm` gives
`e = delta · y` and `Q V² − (Q − 1) y² = 1` (`aux_integral`), as in `P138Adjacent`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCAdjacent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCSquares LCBudget
open P138Bootstrap (one_le_of_pos' int_split one_le_abs)
open P138Adjacent (ι_pos)
open ZRowsCoprimeSquares (abs_eq_ι)
open LCNorm (Weight)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- At a zero the budget is positive. -/
theorem budget_pos (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    0 < (𝓡).Budget := by
  linarith [budget_ge ψ wt hp h hwt hz]

/-- At a zero, `B ≥ 1`. -/
theorem B_ge (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    1 ≤ (𝓡).B :=
  one_le_of_pos' (B_pos ψ wt hp h hwt hz)

/-- At a zero, `c⁴ ≥ 1`. -/
theorem c4_ge (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    1 ≤ x 8 ^ 4 := by
  have hc := c_ne ψ wt hp h (budget_pos ψ wt hp h hwt hz)
  have hc2 : 1 ≤ x 8 ^ 2 := by
    have := one_le_abs hc; rw [← sq_abs]; nlinarith
  have h4 : x 8 ^ 4 = x 8 ^ 2 * x 8 ^ 2 := by ring
  rw [h4]; nlinarith

/-- **`Q > 1`** at a zero. -/
theorem Q_gt (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    1 < (𝓡).Q := by
  have hD := Delta_ge8 ψ wt hp h (budget_pos ψ wt hp h hwt hz)
  have hB := B_ge ψ wt hp h hwt hz
  have hc4 := c4_ge ψ wt hp h hwt hz
  have hD2 : 64 ≤ (𝓡).Delta ^ 2 := by nlinarith
  have h1 : 1 ≤ x 8 ^ 4 * (𝓡).B := by nlinarith
  rw [Q_eq]; nlinarith

/-- **The auxiliary ordinate is integral.** -/
theorem aux_integral (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) {e' : V}
    (he : Da p x κ ω Λ ψ wt = ι e' * ι e') (he0 : 0 < e') :
    ∃ y : V, 0 < y ∧ ι e' = ((𝓡).Q - 1) * ι y ∧
      (𝓡).Q * (𝓡).V ^ 2 - ((𝓡).Q - 1) * (ι y) ^ 2 = 1 := by
  have hQ := Q_gt ψ wt hp h hwt hz
  obtain ⟨dn, hdn⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ (𝓡).Q - 1 by linarith)
  have hdn0 : 0 < dn := by
    rcases eq_zero_or_pos dn with h0 | h0
    · rw [h0, map_zero] at hdn; linarith
    · exact h0
  have hDaQ : Da p x κ ω Λ ψ wt = ((𝓡).Q - 1) * ((𝓡).Q * (𝓡).V ^ 2 - 1) := by
    unfold Da; rw [delta_eq, Cy_eq]
  have hCy : 0 < (𝓡).Q * (𝓡).V ^ 2 - 1 := by
    have hDa : 0 < Da p x κ ω Λ ψ wt := by rw [he]; exact mul_pos (ι_pos he0) (ι_pos he0)
    rw [hDaQ] at hDa
    exact pos_of_mul_pos_right hDa (by linarith)
  have hV : (𝓡).V ≠ 0 := by
    intro h0; rw [h0] at hCy; linarith [show (𝓡).Q * (0 : DiffRing V) ^ 2 - 1 = -1 by ring]
  obtain ⟨vn, hvn⟩ := abs_eq_ι (𝓡).V
  have hvn0 : 0 < vn := by
    rcases eq_zero_or_pos vn with h0 | h0
    · rw [h0, map_zero] at hvn; exact absurd (abs_eq_zero.mp hvn) hV
    · exact h0
  have hVV : |(𝓡).V| * |(𝓡).V| = (𝓡).V ^ 2 := by rw [abs_mul_abs_self]; ring
  have hscaled : (1 + dn) * ((dn * vn) * (dn * vn)) = dn * dn + dn * (e' * e') := by
    apply ι_injective
    simp only [map_add, map_mul, map_one]
    rw [← hdn, ← hvn, ← he, hDaQ]
    linear_combination ((𝓡).Q * ((𝓡).Q - 1) ^ 2) * hVV
  obtain ⟨y, hy, hnorm⟩ :=
    TenPositiveAdjacentInteger.quotient_of_scaled_norm dn dn vn e' hdn0 hdn0 hvn0 hscaled
  have hy0 : 0 < y := by
    rcases eq_zero_or_pos y with h0 | h0
    · rw [h0, mul_zero] at hy; exact absurd hy he0.ne'
    · exact h0
  refine ⟨y, hy0, by rw [hy, map_mul, hdn], ?_⟩
  have h' := congrArg (ι (V := V)) hnorm
  simp only [map_add, map_mul, map_one] at h'
  rw [← hdn, ← hvn, hVV] at h'
  linear_combination h'

end Regs

#print axioms budget_pos
#print axioms Q_gt
#print axioms aux_integral

end DiophantineConsistency.LCAdjacent
