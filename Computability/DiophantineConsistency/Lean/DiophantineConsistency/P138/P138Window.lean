import DiophantineConsistency.P138.P138Budget

/-! # The signed packing window of the rank `R`

`R = (q(q − F) − C)(q² − 1) + (MC + q MF) J` with `q = beta J + 1`. Once the centered budget has
given the common strict signs of `q, F, C, q − F − C` (`P138Budget.centered`), the port bounds
`0 ≤ MC < beta`, `0 ≤ MF < 2 beta` place `R` in the window

    |q| (q² − 1) < R,   R + 2 < q⁴

for either sign of `q` (`window`). For `q < 0` write `Q = −q`, `F' = −F`, `C' = −C`, `J' = −J`:
then `R = (Q(Q − F') + C')(Q² − 1) + J'(Q MF − MC)`, and both cases reduce to `window_core` with
`G = q(q − F) − C ∈ [2|q| − 1, q² − 2]` and `−(|q| + 1) < (MC + q MF) J < 2|q|(|q| + 1)`.

`sizes`: `3R + 1 < |E|`, `R + 1 ≤ |k|` and `4080 ≤ R`, from `|E| = |X||Y| ≥ 4q⁴` and
`k = R + 1 + h E`. This is the signed analogue of the positive windows
`FreeJEarlyWindow.early_window`, `Direct80RankExact.graph_rank_exact`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Window
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing P138Value P138Ports P138Bootstrap P138Budget

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The window, from bounds on `G` and on the column term `T`. -/
theorem window_core (Q G T : DiffRing V) (hQ : 4 ≤ Q) (hGlo : 2 * Q - 1 ≤ G)
    (hGhi : G ≤ Q ^ 2 - 2) (hTlo : -(Q + 1) < T) (hThi : T < 2 * Q * (Q + 1)) :
    Q * (Q ^ 2 - 1) < G * (Q ^ 2 - 1) + T ∧ G * (Q ^ 2 - 1) + T + 2 < Q ^ 4 := by
  have hQ2 : 15 ≤ Q ^ 2 - 1 := by nlinarith
  constructor
  · have h1 : (Q - 1) * (Q ^ 2 - 1) ≤ (G - Q) * (Q ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (Q + 1) * 1 < (Q + 1) * ((Q - 1) ^ 2 - 1) :=
      mul_lt_mul_of_pos_left (by nlinarith) (by linarith)
    nlinarith
  · have h1 : G * (Q ^ 2 - 1) ≤ (Q ^ 2 - 2) * (Q ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right hGhi (by linarith)
    nlinarith

theorem neg_of_mul_pos_neg {a b : DiffRing V} (h : 0 < a * b) (hb : b < 0) : a < 0 := by
  by_contra hc
  have : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt hc) hb.le
  linarith

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓡" => regs p x

/-- The column term `T = (MC + q MF) J` and `beta J = q − 1`. -/
theorem beta_J : p 0 * (𝓡).J = (𝓡).q - 1 := by rw [(qm_eq p x).symm, qm_def]

set_option maxHeartbeats 1000000 in
theorem window_ineq (hp : PortFacts p)
    (hs : 0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q) :
    |(𝓡).q| * ((𝓡).q ^ 2 - 1) < (𝓡).R ∧ (𝓡).R + 2 < (𝓡).q ^ 4 := by
  obtain ⟨hF, hC, hD⟩ := hs
  have hb := beta_pos p hp
  have hMC0 := hp.MC_nonneg
  have hMC := hp.MC_lt
  have hMF0 := hp.MF_nonneg
  have hMF := hp.MF_lt
  have hbJ := beta_J p x
  have hq64 := abs_q_ge p x hp
  have h64 : (4 : DiffRing V) ≤ 2 ^ 64 := by norm_num
  have hqne := q_ne p x hp
  rw [R_eq]
  set q := (𝓡).q with hqdef
  set F := (𝓡).F
  set C := x 1
  set J := (𝓡).J
  rcases lt_or_gt_of_ne hqne with hneg | hpos
  · -- `q < 0`: `Q = −q`
    have hQ : 4 ≤ -q := by rw [abs_of_neg hneg] at hq64; linarith
    have hF' : 1 ≤ -F := one_le_of_pos' (neg_pos.mpr (neg_of_mul_pos_neg hF hneg))
    have hC' : 1 ≤ -C := one_le_of_pos' (neg_pos.mpr (neg_of_mul_pos_neg hC hneg))
    have hD' : 1 ≤ -(q - F - C) := one_le_of_pos' (neg_pos.mpr (neg_of_mul_pos_neg hD hneg))
    have hJ : 0 < -J := by
      by_contra hc
      have : 0 ≤ p 0 * J := mul_nonneg hb.le (by linarith)
      linarith
    have hG : q * (q - F) - C = (-q) * ((-q) - (-F)) + (-C) := by ring
    have hGlo : 2 * (-q) - 1 ≤ q * (q - F) - C := by
      rw [hG]
      have : (-q) * 2 ≤ (-q) * (-(q - F - C) + (-C)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    have hGhi : q * (q - F) - C ≤ (-q) ^ 2 - 2 := by
      rw [hG]
      have : (-q) * 1 ≤ (-q) * (-F) := mul_le_mul_of_nonneg_left hF' (by linarith)
      linarith
    -- `T p0 = (Q MF − MC)(Q + 1)`
    have hT : (p 2 + q * p 3) * J * p 0 = ((-q) * p 3 - p 2) * (-q + 1) := by
      have : J * p 0 = q - 1 := by rw [mul_comm]; exact hbJ
      calc (p 2 + q * p 3) * J * p 0 = (p 2 + q * p 3) * (J * p 0) := by ring
        _ = _ := by rw [this]; ring
    have hTlo : -(-q + 1) < (p 2 + q * p 3) * J := by
      have h1 : -p 0 * (-q + 1) < ((-q) * p 3 - p 2) * (-q + 1) := by
        apply mul_lt_mul_of_pos_right _ (by linarith)
        have : 0 ≤ (-q) * p 3 := mul_nonneg (by linarith) hMF0
        linarith
      by_contra hc
      have h2 : (p 2 + q * p 3) * J * p 0 ≤ -(-q + 1) * p 0 :=
        mul_le_mul_of_nonneg_right (le_of_not_gt hc) hb.le
      rw [hT] at h2
      linarith
    have hThi : (p 2 + q * p 3) * J < 2 * (-q) * (-q + 1) := by
      have h1 : ((-q) * p 3 - p 2) * (-q + 1) < (2 * p 0 * (-q)) * (-q + 1) := by
        apply mul_lt_mul_of_pos_right _ (by linarith)
        have : (-q) * p 3 < (-q) * (2 * p 0) := mul_lt_mul_of_pos_left hMF (by linarith)
        linarith
      by_contra hc
      have h2 : 2 * (-q) * (-q + 1) * p 0 ≤ (p 2 + q * p 3) * J * p 0 :=
        mul_le_mul_of_nonneg_right (le_of_not_gt hc) hb.le
      rw [hT] at h2
      linarith
    have hcore := window_core (-q) (q * (q - F) - C) ((p 2 + q * p 3) * J) hQ hGlo hGhi
      (by linarith) (by linarith)
    rw [abs_of_neg hneg]
    have e2 : (-q) ^ 2 = q ^ 2 := by ring
    have e4 : (-q) ^ 4 = q ^ 4 := by ring
    rw [e2, e4] at hcore
    exact hcore
  · -- `q > 0`
    have hQ : 4 ≤ q := by rw [abs_of_pos hpos] at hq64; linarith
    have hF' : 1 ≤ F := one_le_of_pos' (pos_of_mul_pos_left hF hpos.le)
    have hC' : 1 ≤ C := one_le_of_pos' (pos_of_mul_pos_left hC hpos.le)
    have hD' : 1 ≤ q - F - C := one_le_of_pos' (pos_of_mul_pos_left hD hpos.le)
    have hJ : 0 < J := by
      by_contra hc
      have : p 0 * J ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le (by linarith)
      linarith
    have hGlo : 2 * q - 1 ≤ q * (q - F) - C := by
      have h1 : q * 1 ≤ q * (q - F - C) := mul_le_mul_of_nonneg_left hD' hpos.le
      have h2 : 1 * (q - 1) ≤ C * (q - 1) := mul_le_mul_of_nonneg_right hC' (by linarith)
      linarith
    have hGhi : q * (q - F) - C ≤ q ^ 2 - 2 := by
      have : q * 1 ≤ q * F := mul_le_mul_of_nonneg_left hF' hpos.le
      linarith
    have hT : (p 2 + q * p 3) * J * p 0 = (p 2 + q * p 3) * (q - 1) := by
      have : J * p 0 = q - 1 := by rw [mul_comm]; exact hbJ
      calc (p 2 + q * p 3) * J * p 0 = (p 2 + q * p 3) * (J * p 0) := by ring
        _ = _ := by rw [this]
    have hT0 : 0 ≤ (p 2 + q * p 3) * J :=
      mul_nonneg (add_nonneg hMC0 (mul_nonneg hpos.le hMF0)) hJ.le
    have hThi : (p 2 + q * p 3) * J < 2 * q * (q + 1) := by
      have h1 : (p 2 + q * p 3) * (q - 1) < (p 0 * (1 + 2 * q)) * (q - 1) := by
        apply mul_lt_mul_of_pos_right _ (by linarith)
        have : q * p 3 < q * (2 * p 0) := mul_lt_mul_of_pos_left hMF hpos
        linarith
      by_contra hc
      have h2 : 2 * q * (q + 1) * p 0 ≤ (p 2 + q * p 3) * J * p 0 :=
        mul_le_mul_of_nonneg_right (le_of_not_gt hc) hb.le
      rw [hT] at h2
      have h3 : 0 ≤ p 0 * (3 * q + 1) := mul_nonneg hb.le (by linarith)
      linarith
    have hcore := window_core q (q * (q - F) - C) ((p 2 + q * p 3) * J) hQ hGlo hGhi
      (by linarith) hThi
    rw [abs_of_pos hpos]
    exact hcore

/-- **The signed window**: `R` is a natural number with `|q| (q² − 1) < R` and `R + 2 < q⁴`. -/
theorem window (hp : PortFacts p)
    (hs : 0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q) :
    ∃ Rn : V, (𝓡).R = ι Rn ∧ |(𝓡).q| * ((𝓡).q ^ 2 - 1) < ι Rn ∧ ι Rn + 2 < (𝓡).q ^ 4 := by
  obtain ⟨h1, h2⟩ := window_ineq p x hp hs
  have h0 : 0 ≤ (𝓡).R := by
    have : 0 ≤ |(𝓡).q| * ((𝓡).q ^ 2 - 1) := by
      have := abs_q_ge p x hp
      have h64 : (2 : DiffRing V) ≤ 2 ^ 64 := by norm_num
      have : 1 ≤ (𝓡).q ^ 2 := by rw [← sq_abs]; nlinarith
      exact mul_nonneg (abs_nonneg _) (by linarith)
    linarith
  obtain ⟨Rn, hRn⟩ := nonneg_iff.mp h0
  exact ⟨Rn, hRn, by rw [← hRn]; exact h1, by rw [← hRn]; exact h2⟩

/-- **Sizes**: `3R + 1 < |E|`, `R + 1 ≤ |k|`, `4080 ≤ R`. -/
theorem sizes (hp : PortFacts p)
    (hs : 0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q) :
    3 * (𝓡).R + 1 < |(𝓡).E| ∧ (𝓡).R + 1 ≤ |(𝓡).k| ∧ 4080 ≤ (𝓡).R := by
  obtain ⟨h1, h2⟩ := window_ineq p x hp hs
  have hq := abs_q_ge p x hp
  have h64 : (4096 : DiffRing V) ≤ 2 ^ 64 := by norm_num
  have hq1 : 1 ≤ |(𝓡).q| := by linarith
  have hq2 : 2 ≤ (𝓡).q ^ 2 - 1 := by rw [← sq_abs]; nlinarith
  have hR : 4080 ≤ (𝓡).R := by
    have := mul_le_mul (by linarith : (4096:DiffRing V) ≤ |(𝓡).q|) hq2 (by norm_num) (abs_nonneg _)
    linarith
  have hE : 4 * (𝓡).q ^ 4 ≤ |(𝓡).E| := by
    rw [E_def, abs_mul]
    have hX := abs_X p x hp
    have hY := abs_Y p x hp
    have e : (𝓡).q ^ 4 = |(𝓡).q| * |(𝓡).q| ^ 3 := by
      have h4 : |(𝓡).q| ^ 4 = (𝓡).q ^ 4 := by
        rw [show |(𝓡).q| ^ 4 = (|(𝓡).q| ^ 2) ^ 2 by ring, sq_abs]; ring
      rw [← h4]; ring
    rw [e]
    have : 0 ≤ |(𝓡).q| ^ 3 := pow_nonneg (abs_nonneg _) 3
    calc 4 * (|(𝓡).q| * |(𝓡).q| ^ 3) = (4 * |(𝓡).q|) * |(𝓡).q| ^ 3 := by ring
      _ ≤ |(𝓡).X| * |(𝓡).Y| := mul_le_mul hX hY this (abs_nonneg _)
  have hE3 : 3 * (𝓡).R + 1 < |(𝓡).E| := by
    have : 0 ≤ (𝓡).q ^ 4 := by rw [show (𝓡).q ^ 4 = ((𝓡).q ^ 2) ^ 2 by ring]; exact sq_nonneg _
    linarith
  refine ⟨hE3, ?_, hR⟩
  rw [k_eq]
  by_cases hh : x 3 = 0
  · rw [hh, zero_mul, add_zero]; exact le_of_eq (abs_of_nonneg (by linarith)).symm
  · have h1' : |(𝓡).E| ≤ |x 3 * (𝓡).E| := by
      rw [abs_mul]; exact le_mul_of_one_le_left (abs_nonneg _) (one_le_abs hh)
    have h3 : |x 3 * (𝓡).E| - ((𝓡).R + 1) ≤ |(𝓡).R + 1 + x 3 * (𝓡).E| := by
      have := abs_sub_abs_le_abs_sub (x 3 * (𝓡).E) (-((𝓡).R + 1))
      rw [abs_neg, abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ (𝓡).R + 1)] at this
      rw [show x 3 * (𝓡).E - -((𝓡).R + 1) = (𝓡).R + 1 + x 3 * (𝓡).E by ring] at this
      exact this
    linarith

end Regs

#print axioms window_core
#print axioms window_ineq
#print axioms window
#print axioms sizes

end DiophantineConsistency.P138Window
