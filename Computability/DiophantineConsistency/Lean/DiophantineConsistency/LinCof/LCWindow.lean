import DiophantineConsistency.LinCof.LCBudget
import DiophantineConsistency.P138.P138Window

/-! # The signed packing window of the rank `R`, and the index modulus of the `k` slot

`R = (q(q − F) − C)(q² − 1) + (MC + q MF) J` with `q = beta J + 1` does not involve the free
scale. Once the centered budget has given the common strict signs of `q, F, C, q − F − C`
(`LCBudget.centered`), the port bounds place `R` in the window

    |q| (q² − 1) < R,   R + 2 < q⁴

for either sign of `q` (`window_ineq`, `window`; the core inequality is
`P138Window.window_core`), and `4080 ≤ R` (`R_ge`).

**The index modulus.** The one place where the definition of the `k` slot enters soundness
(beyond the slot law) is `IndexModulus`: `κ = R + 1 + h μ` with `μ ∣ X Y²` and, *once the scale
bound `|q|^(2+e) < |Y|` of `LCBudget.abs_Y_gt` is known*, `4q⁴ ≤ |μ|`. Unlike package 138 the
size of `μ` is not unconditional, because `Y` is a free unknown.

* 298/146: `μ = X Y²` (`modulus298`; `|X| Y² ≥ 4|q| · q⁴`);
* 300/144: `μ = X Y` (`modulus300`; `|X| |Y| ≥ 4|q| · |q|³`).

With the window, `modulus` gives a natural `m = |μ|` with `m ∣ X Y²`, `m ∣ k − (R + 1)` and
`3R + 1 < m`; then `R + 1 ≤ |k|` (`k_ge`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCBudget
open P138Bootstrap (one_le_of_pos' int_split one_le_abs)
open P138Window (window_core neg_of_mul_pos_neg)
open ZRowsCoprimeSquares (abs_eq_ι)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem abs_pow_four (q : DiffRing V) : |q| ^ 4 = q ^ 4 := Even.pow_abs ⟨2, rfl⟩ q

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- `beta J = q − 1`. -/
theorem beta_J : p 0 * (𝓡).J = (𝓡).q - 1 := by rw [(qm_eq p x κ ω Λ ψ wt).symm, qm_def]

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
  have hbJ := beta_J p x κ ω Λ ψ wt
  have hq64 := abs_q_ge p x κ ω Λ ψ wt hp
  have h64 : (4 : DiffRing V) ≤ 2 ^ 64 := by norm_num
  have hqne := q_ne p x κ ω Λ ψ wt hp
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
  obtain ⟨h1, h2⟩ := window_ineq p x κ ω Λ ψ wt hp hs
  have h0 : 0 ≤ (𝓡).R := by
    have : 0 ≤ |(𝓡).q| * ((𝓡).q ^ 2 - 1) := by
      have := abs_q_ge p x κ ω Λ ψ wt hp
      have h64 : (2 : DiffRing V) ≤ 2 ^ 64 := by norm_num
      have : 1 ≤ (𝓡).q ^ 2 := by rw [← sq_abs]; nlinarith
      exact mul_nonneg (abs_nonneg _) (by linarith)
    linarith
  obtain ⟨Rn, hRn⟩ := nonneg_iff.mp h0
  exact ⟨Rn, hRn, by rw [← hRn]; exact h1, by rw [← hRn]; exact h2⟩

/-- `4080 ≤ R`, from the window and `|q| ≥ 2^64`. -/
theorem R_ge (hp : PortFacts p)
    (hs : 0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q) :
    4080 ≤ (𝓡).R := by
  obtain ⟨h1, _⟩ := window_ineq p x κ ω Λ ψ wt hp hs
  have hq := abs_q_ge p x κ ω Λ ψ wt hp
  have h64 : (4096 : DiffRing V) ≤ 2 ^ 64 := by norm_num
  have hq2 : 2 ≤ (𝓡).q ^ 2 - 1 := by rw [← sq_abs]; nlinarith
  have := mul_le_mul (by linarith : (4096:DiffRing V) ≤ |(𝓡).q|) hq2 (by norm_num) (abs_nonneg _)
  linarith

/-- **An index modulus of the `k` slot**: `κ = R + 1 + hμ` with `μ ∣ X Y²` and, under the scale
bound `|q|^(2+e) < |Y|`, `4q⁴ ≤ |μ|`. With the slot law this is all that soundness uses about
the slots. -/
def IndexModulus (e : ℕ) : Prop :=
  ∃ μ h : DiffRing V, κ = (𝓡).R + 1 + h * μ ∧ μ ∣ (𝓡).X * (𝓡).Y ^ 2 ∧
    (|(𝓡).q| ^ (2 + e) < |(𝓡).Y| → 4 * (𝓡).q ^ 4 ≤ |μ|)

/-- `4q⁴ ≤ |X Y²|` when `q² < |Y|`. -/
theorem four_q4_le_ell (hp : PortFacts p) (hY : |(𝓡).q| ^ 2 < |(𝓡).Y|) :
    4 * (𝓡).q ^ 4 ≤ |(𝓡).X * (𝓡).Y ^ 2| := by
  rw [abs_mul, abs_pow, ← abs_pow_four]
  have hX := abs_X p x κ ω Λ ψ wt
  have hq1 : (1 : DiffRing V) ≤ |(𝓡).q| := one_le_abs (q_ne p x κ ω Λ ψ wt hp)
  have h2 : (|(𝓡).q| ^ 2) ^ 2 ≤ |(𝓡).Y| ^ 2 := pow_le_pow_left₀ (by positivity) hY.le 2
  have e4 : (|(𝓡).q| ^ 2) ^ 2 = |(𝓡).q| ^ 4 := by ring
  rw [e4] at h2
  have h4 : 0 ≤ |(𝓡).q| ^ 4 := by positivity
  calc 4 * |(𝓡).q| ^ 4 = 4 * 1 * |(𝓡).q| ^ 4 := by ring
    _ ≤ 4 * |(𝓡).q| * |(𝓡).q| ^ 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq1 (by norm_num)) h4
    _ ≤ |(𝓡).X| * |(𝓡).Y| ^ 2 := mul_le_mul hX h2 h4 (abs_nonneg _)

/-- `4q⁴ ≤ |X Y|` when `|q|³ < |Y|`. -/
theorem four_q4_le_E (hY : |(𝓡).q| ^ 3 < |(𝓡).Y|) :
    4 * (𝓡).q ^ 4 ≤ |(𝓡).X * (𝓡).Y| := by
  rw [abs_mul, ← abs_pow_four]
  have hX := abs_X p x κ ω Λ ψ wt
  have h3 : 0 ≤ |(𝓡).q| ^ 3 := by positivity
  calc 4 * |(𝓡).q| ^ 4 = 4 * |(𝓡).q| * |(𝓡).q| ^ 3 := by ring
    _ ≤ |(𝓡).X| * |(𝓡).Y| := mul_le_mul hX hY.le h3 (abs_nonneg _)

end Regs

section Forms
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (ψ wt : DiffRing V)
local notation "𝓐" => regsK p x (k298 p x) (kq298 p x) (L298 p x) ψ wt
local notation "𝓑" => regsK p x (k300 p x) (kq300 p x) (L300 p x) ψ wt

/-- The 298/146 index `k = R + 1 + h · X Y²` has the modulus `μ = X Y²` (for every center and
weight). -/
theorem modulus298 (hp : PortFacts p) :
    IndexModulus p x (k298 p x) (kq298 p x) (L298 p x) ψ wt 0 :=
  ⟨(𝓐).X * (𝓐).Y ^ 2, x 3, k298_eq p x, dvd_refl _,
    fun hY => four_q4_le_ell p x _ _ _ ψ wt hp hY⟩

/-- The 300/144 index `k = R + 1 + h · X Y` has the modulus `μ = X Y`, which divides `X Y²`
(for every center and weight). -/
theorem modulus300 :
    IndexModulus p x (k300 p x) (kq300 p x) (L300 p x) ψ wt 1 :=
  ⟨(𝓑).X * (𝓑).Y, x 3, k300_eq p x, ⟨(𝓑).Y, by ring⟩,
    fun hY => four_q4_le_E p x _ _ _ ψ wt hY⟩

end Forms

section Zero
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- The common signs, from a positive budget (`LCBudget.centered`). -/
theorem signs (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hB : 0 < (𝓡).Budget) :
    0 < (𝓡).F * (𝓡).q ∧ 0 < x 1 * (𝓡).q ∧ 0 < ((𝓡).q - (𝓡).F - x 1) * (𝓡).q := by
  obtain ⟨_, _, _, h1, h2, h3, _⟩ := centered ψ wt hp h hB
  exact ⟨h1, h2, h3⟩

/-- **The index modulus in natural form**: a natural `m = |μ|` with `m ∣ X Y²`,
`m ∣ k − (R + 1)` and `3R + 1 < m`. -/
theorem modulus (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hκ : IndexModulus p x κ ω Λ ψ wt e)
    (hB : 0 < (𝓡).Budget) :
    ∃ m : V, (ι m : DiffRing V) ∣ (𝓡).X * (𝓡).Y ^ 2 ∧ (ι m : DiffRing V) ∣ (𝓡).k - ((𝓡).R + 1) ∧
      3 * (𝓡).R + 1 < ι m := by
  obtain ⟨μ, t, hk, hdvd, hge⟩ := hκ
  have hge := hge (abs_Y_gt ψ wt hp h hB)
  have hs := signs ψ wt hp h hB
  obtain ⟨m, hm⟩ := abs_eq_ι μ
  obtain ⟨_, h2⟩ := window_ineq p x κ ω Λ ψ wt hp hs
  have hR := R_ge p x κ ω Λ ψ wt hp hs
  refine ⟨m, ?_, ?_, ?_⟩
  · rw [← hm]; exact (abs_dvd μ _).mpr hdvd
  · have e' : (𝓡).k - ((𝓡).R + 1) = μ * t := by rw [k_reg]; linear_combination hk
    rw [← hm, e']
    exact dvd_mul_of_dvd_left (abs_dvd_self μ) t
  · have : 0 ≤ (𝓡).q ^ 4 := by positivity
    rw [← hm]
    linarith

/-- `R + 1 ≤ |k|`: `k ≡ R + 1 (mod m)` with `0 < R + 1 < m − 2R`. -/
theorem k_ge (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hκ : IndexModulus p x κ ω Λ ψ wt e)
    (hB : 0 < (𝓡).Budget) : (𝓡).R + 1 ≤ |(𝓡).k| := by
  obtain ⟨m, _, ⟨d, hd⟩, hm⟩ := modulus ψ wt hp h hκ hB
  have hR := R_ge p x κ ω Λ ψ wt hp (signs ψ wt hp h hB)
  have hk : (𝓡).k = (𝓡).R + 1 + ι m * d := by linear_combination hd
  rw [hk]
  by_cases hd0 : d = 0
  · rw [hd0, mul_zero, add_zero]; exact le_of_eq (abs_of_nonneg (by linarith)).symm
  · have h1' : (ι m : DiffRing V) ≤ |ι m * d| := by
      rw [abs_mul, abs_of_nonneg (ι_nonneg m)]
      exact le_mul_of_one_le_right (ι_nonneg m) (one_le_abs hd0)
    have h3 : |ι m * d| - ((𝓡).R + 1) ≤ |(𝓡).R + 1 + ι m * d| := by
      have := abs_sub_abs_le_abs_sub (ι m * d) (-((𝓡).R + 1))
      rw [abs_neg, abs_of_nonneg (by linarith : (0 : DiffRing V) ≤ (𝓡).R + 1)] at this
      rw [show ι m * d - -((𝓡).R + 1) = (𝓡).R + 1 + ι m * d by ring] at this
      exact this
    linarith

end Zero

#print axioms window_ineq
#print axioms window
#print axioms R_ge
#print axioms modulus298
#print axioms modulus300
#print axioms modulus
#print axioms k_ge

end DiophantineConsistency.LCWindow
