import IPRADerivations.Analysis.Stirling.Wallis.WallisGrid
import IPRADerivations.Analysis.RationalArithmetic.PowerIncrement

/-!
# The finite Wallis recurrence

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Section `sec:wallis`, `eq:Jrec`:
for `J_k(M) = (1/M) ∑_{j<M} w(j/M) s(j/M)^k`,
`|(k − 1) J_{k−2}(M) − k J_k(M)| ≤ 8k²/M` (`k ≥ 2`).

With the samples of `WallisGrid` (cleared by `F = L!`, `2M² ≤ L`), `𝒥_k = ∑_{j<M} om_j sg_j^k = M F^{k+1} J_k(M)`
and the statement is `|(k − 1) F² 𝒥_{k−2} − k 𝒥_k| ≤ 8k² F^{k+1}`. Write `k = i + 2`.

The paper integrates `G_k = c s^{k−1}` by parts. On a cell `j → j + 1`, with `G = gm · sg^{i+1}`,
`H⁺ = om (i + 1) gm² sg^i` and `H⁻ = om · sg^{i+2}` (so that `H⁺ − H⁻ = F^{i+3} H_k`):

* `cell_ring`: the exact identity
  `T D (M F (G' − G) − (H⁺ − H⁻)) = M² F (D c (c + c') ds · kd + 2j s^{i+2} − D (i+1) c s^i dc
     − D ds (s'^{i+1} + 2 s · gd) − 2j (i+1) c² s^i)`,
  with `T = M² + j(j+1)`, `D = M² + j²`, `ds = s' − s`, `dc = c − c'`, from the rotation identities
  `sg_step`, `gm_step` and the first- and second-order power sums `gd`, `kd`;
* `cell_up`, `cell_dn`: `M (M F G' + H⁻) ≤ M (M F G + H⁺) + (2i(i+1) + 2) F^{i+3}` and
  `M (M F G + H⁺) ≤ M (M F G' + H⁻) + (8(i+1) + 2) F^{i+3}`, i.e. the cell error of the paper is between
  `−(8k − 6) h²` and `(2k² − 6k + 6) h²`, within its bound `8k² h²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.WallisRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselQuadrature (uq d_pos lift4 inst2_lift4)
open LeanProofs.IPRA.Analysis.BaselCore (sum_lin)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Analysis.WallisGrid
open LeanProofs.IPRA.Algebra.PowerDifference (gd power_diff gd_le)
open LeanProofs.IPRA.Analysis.PowerIncrement (kd gd_kd kd_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The cell identity -/

/-- The exact error of one cell of the integration by parts, as a ring identity. -/
theorem cell_ring {R : Type*} [CommRing R] (M F T D j s s' c c' ω i S0 S1 S2 S1' g k : R)
    (hT : T = D + j) (r1 : T * s' = T * s + M * (c + c')) (r2 : T * c = T * c' + M * (s + s'))
    (r3 : S1' + s * g = S1 + s' * g) (r4 : g + s * k = (i + 1) * S0 + s' * k)
    (r5 : ω * D = 2 * (M * M) * F) (r6 : S2 = S1 * s) :
    T * D * (M * F * (c' * S1' - c * S1) - (ω * ((i + 1) * (c * c) * S0) - ω * S2)) =
      M * M * F * (D * c * (c + c') * (s' - s) * k + 2 * j * S2 - D * (i + 1) * c * S0 * (c - c')
        - D * (s' - s) * (S1' + 2 * s * g) - 2 * j * (i + 1) * (c * c) * S0) := by
  linear_combination (D * M * F * T * c - 2 * M * M * F * D * s) * r3 + (D * M * F * c * g) * r1
    - (D * M * F * S1') * r2 - (T * ((i + 1) * (c * c) * S0 - S2)) * r5
    + (M * M * F * D * c * (c + c')) * r4 - (2 * M * M * F * ((i + 1) * (c * c) * S0 - S2)) * hT
    + (2 * M * M * F * D) * r6

/-- `om · D = 2M² F`. -/
theorem om_D {j M₀ L : PTm n} (hj : Γ ⊢[PRAAx] le j (succ M₀))
    (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] om j (succ M₀) L * (succ M₀ * succ M₀ + j * j) ≐ two * (succ M₀ * succ M₀) * fact L := by
  have ue := natEq (u_eq_le hj hL)
  apply deriveNat; simp only [om]; ipra_simps
  rw [ue]; ring

/-! ## One cell -/

section cell

variable {i j M₀ L : PTm n}

local notation "s₀" => sg j (succ M₀) L
local notation "s₁" => sg (succ j) (succ M₀) L
local notation "c₀" => gm j (succ M₀) L
local notation "c₁" => gm (succ j) (succ M₀) L
local notation "ω₀" => om j (succ M₀) L
local notation "𝔉" => fact L
local notation "𝔐" => succ M₀
local notation "𝔗" => (succ M₀ * succ M₀ + j * succ j)
local notation "𝔇" => (succ M₀ * succ M₀ + j * j)

/-- `M · j ≤ M² + j²`. -/
theorem Mj_le (hj : Γ ⊢[PRAAx] le j 𝔐) : Γ ⊢[PRAAx] le (𝔐 * j) 𝔇 := by
  ipra_le (𝔞 M₀ + 1) * sl hj + 𝔞 j * 𝔞 j

/-- `M (s' − s) ≤ 2F` for the term `s' ∸ s`. -/
theorem ds_le (hj : Γ ⊢[PRAAx] le (succ j) 𝔐) (hL : Γ ⊢[PRAAx] le (two * (𝔐 * 𝔐)) L) :
    Γ ⊢[PRAAx] le (𝔐 * monus s₁ s₀) (two * 𝔉) := by
  have e := natEq (eq_add_of_le (sg_mono hj hL))
  have h := sg_inc hj hL
  ipra_le sl h with (𝔞 M₀ + 1) * e

/-- `M (c − c') ≤ 2F` for the term `c ∸ c'`. -/
theorem dc_le (hj : Γ ⊢[PRAAx] le (succ j) 𝔐) (hL : Γ ⊢[PRAAx] le (two * (𝔐 * 𝔐)) L) :
    Γ ⊢[PRAAx] le (𝔐 * monus c₀ c₁) (two * 𝔉) := by
  have e := natEq (eq_add_of_le (gm_anti hj hL))
  have h := gm_inc hj hL
  ipra_le sl h with (𝔞 M₀ + 1) * e

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- The upper cell estimate: `M (M F G' + H⁻) ≤ M (M F G + H⁺) + (2i(i+1) + 2) F^{i+3}`. -/
theorem cell_up (hj : Γ ⊢[PRAAx] le (succ j) 𝔐) (hL : Γ ⊢[PRAAx] le (two * (𝔐 * 𝔐)) L) :
    Γ ⊢[PRAAx] le (𝔐 * (𝔐 * 𝔉 * (c₁ * pw s₁ (succ i)) + ω₀ * pw s₀ (succ (succ i))))
      (𝔐 * (𝔐 * 𝔉 * (c₀ * pw s₀ (succ i)) + ω₀ * (succ i * (c₀ * c₀) * pw s₀ i)) +
        (two * (i * succ i) + two) * pw 𝔉 (succ (succ (succ i)))) := by
  have hj0 : Γ ⊢[PRAAx] le j 𝔐 := le_trans (le_succ_self j) hj
  have bc0 := gm_le hj0 hL; have bc1 := gm_le hj hL
  have bs0 := sg_le hj0 hL; have bs1 := sg_le hj hL
  have bcc : Γ ⊢[PRAAx] le (c₀ + c₁) (two * 𝔉) := by ipra_le sl bc0 + sl bc1
  have pP1 := le_mul_mono bc0 (le_mul_mono bcc (le_mul_mono (ds_le hj hL) (kd_le (Γ := Γ) i bs1 bs0)))
  have pP2 := le_mul_mono (Mj_le hj0) (pw_le_pw (succ (succ i)) bs0)
  have r1 := natEq (sg_step hj hL); have r2 := natEq (gm_step hj hL)
  have r3 := natEq (power_diff (Γ := Γ) s₁ s₀ (succ i))
  have r4 := natEq (gd_kd (Γ := Γ) s₁ s₀ i)
  have r5 := natEq (om_D hj0 hL)
  have r6 := natEq (pw_succ (Γ := Γ) s₀ (succ i))
  have f1 := natEq (pw_succ (Γ := Γ) 𝔉 i); have f2 := natEq (pw_succ (Γ := Γ) 𝔉 (succ i))
  have f3 := natEq (pw_succ (Γ := Γ) 𝔉 (succ (succ i)))
  have eds := natEq (eq_add_of_le (sg_mono hj hL)); have edc := natEq (eq_add_of_le (gm_anti hj hL))
  refine mul_le_cancel (d' := one) (mul_le_cancel (d' := M₀ * M₀ + two * M₀ + j * succ j)
    (le_congr (congrMul (T_pos j M₀) (.eqRefl _)) (congrMul (T_pos j M₀) (.eqRefl _))
      (mul_le_cancel (d' := pred 𝔇) (le_congr (congrMul (d_pos j M₀) (.eqRefl _))
        (congrMul (d_pos j M₀) (.eqRefl _)) ?_))))
  ipra_le 𝔞 j * (𝔞 j + 1) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * (4 * (𝔞 i * (𝔞 i + 1))) *
        𝔞 (pw 𝔉 (succ (succ (succ i)))) +
      (𝔞 M₀ + 1) * (𝔞 M₀ + 1) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * sl pP1 +
      4 * (𝔞 j * (𝔞 j + 1) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * 𝔞 (pw 𝔉 (succ (succ (succ i)))) +
        (𝔞 M₀ + 1) * (𝔞 M₀ + 1) * 𝔞 𝔉 * sl pP2) +
      2 * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) * (𝔞 M₀ + 1)) * 𝔞 𝔉 *
        (((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * (𝔞 i + 1) * 𝔞 c₀ * 𝔞 (pw s₀ i) * 𝔞 (monus c₀ c₁) +
          ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * 𝔞 (monus s₁ s₀) *
            (𝔞 (pw s₁ (succ i)) + 2 * 𝔞 s₀ * 𝔞 (gd s₁ s₀ (succ i))) +
          2 * 𝔞 j * (𝔞 i + 1) * (𝔞 c₀ * 𝔞 c₀) * 𝔞 (pw s₀ i)) using
    have hds : 𝔞 (monus s₁ s₀) = 𝔞 s₁ - 𝔞 s₀ := by linear_combination -eds
    have hdc : 𝔞 (monus c₀ c₁) = 𝔞 c₀ - 𝔞 c₁ := by linear_combination -edc
    have X := cell_ring (𝔞 M₀ + 1) (𝔞 𝔉) ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * (𝔞 j + 1))
      ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) (𝔞 j) (𝔞 s₀) (𝔞 s₁) (𝔞 c₀) (𝔞 c₁) (𝔞 ω₀) (𝔞 i)
      (𝔞 (pw s₀ i)) (𝔞 (pw s₀ (succ i))) (𝔞 (pw s₀ (succ (succ i)))) (𝔞 (pw s₁ (succ i)))
      (𝔞 (gd s₁ s₀ (succ i))) (𝔞 (kd s₁ s₀ i)) (by ring) (by linear_combination r1)
      (by linear_combination r2) (by linear_combination r3) (by linear_combination r4)
      (by linear_combination r5) (by linear_combination r6)
    rw [hds, hdc, f3, f2, f1]
    generalize (𝔞 M₀ + 1) = Mv at X ⊢
    generalize Mv * Mv + 𝔞 j * 𝔞 j = Dv at X ⊢
    linear_combination (-2 * Mv) * X

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- The lower cell estimate: `M (M F G + H⁺) ≤ M (M F G' + H⁻) + (8(i+1) + 2) F^{i+3}`. -/
theorem cell_dn (hj : Γ ⊢[PRAAx] le (succ j) 𝔐) (hL : Γ ⊢[PRAAx] le (two * (𝔐 * 𝔐)) L) :
    Γ ⊢[PRAAx] le (𝔐 * (𝔐 * 𝔉 * (c₀ * pw s₀ (succ i)) + ω₀ * (succ i * (c₀ * c₀) * pw s₀ i)))
      (𝔐 * (𝔐 * 𝔉 * (c₁ * pw s₁ (succ i)) + ω₀ * pw s₀ (succ (succ i))) +
        (num 8 * succ i + two) * pw 𝔉 (succ (succ (succ i)))) := by
  have hj0 : Γ ⊢[PRAAx] le j 𝔐 := le_trans (le_succ_self j) hj
  have bc0 := gm_le hj0 hL
  have bs0 := sg_le hj0 hL; have bs1 := sg_le hj hL
  have pN1 := le_mul_mono bc0 (le_mul_mono (pw_le_pw i bs0) (dc_le hj hL))
  have pN2 := le_mul_mono (ds_le hj hL) (add_le_add₂ (pw_le_pw (succ i) bs1)
    (le_mul_mono (le_mul_mono (le_refl two) bs0) (gd_le (Γ := Γ) i bs1 bs0)))
  have pN3 := le_mul_mono (Mj_le hj0) (le_mul_mono (le_mul_mono bc0 bc0) (pw_le_pw i bs0))
  have r1 := natEq (sg_step hj hL); have r2 := natEq (gm_step hj hL)
  have r3 := natEq (power_diff (Γ := Γ) s₁ s₀ (succ i))
  have r4 := natEq (gd_kd (Γ := Γ) s₁ s₀ i)
  have r5 := natEq (om_D hj0 hL)
  have r6 := natEq (pw_succ (Γ := Γ) s₀ (succ i))
  have f1 := natEq (pw_succ (Γ := Γ) 𝔉 i); have f2 := natEq (pw_succ (Γ := Γ) 𝔉 (succ i))
  have f3 := natEq (pw_succ (Γ := Γ) 𝔉 (succ (succ i)))
  have eds := natEq (eq_add_of_le (sg_mono hj hL)); have edc := natEq (eq_add_of_le (gm_anti hj hL))
  refine mul_le_cancel (d' := one) (mul_le_cancel (d' := M₀ * M₀ + two * M₀ + j * succ j)
    (le_congr (congrMul (T_pos j M₀) (.eqRefl _)) (congrMul (T_pos j M₀) (.eqRefl _))
      (mul_le_cancel (d' := pred 𝔇) (le_congr (congrMul (d_pos j M₀) (.eqRefl _))
        (congrMul (d_pos j M₀) (.eqRefl _)) ?_))))
  ipra_le 2 * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) * (𝔞 M₀ + 1)) * 𝔞 𝔉 *
        (((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * 𝔞 c₀ * (𝔞 c₀ + 𝔞 c₁) * 𝔞 (monus s₁ s₀) * 𝔞 (kd s₁ s₀ i) +
          2 * 𝔞 j * 𝔞 (pw s₀ (succ (succ i)))) +
      2 * (8 * (𝔞 i + 1) + 2) * (𝔞 j * (𝔞 j + 1) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) *
        𝔞 (pw 𝔉 (succ (succ (succ i))))) +
      2 * (𝔞 i + 1) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * 𝔞 𝔉) * sl pN1 +
      2 * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * 𝔞 𝔉) * sl pN2 +
      4 * (𝔞 i + 1) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) * 𝔞 𝔉) * sl pN3 using
    have hds : 𝔞 (monus s₁ s₀) = 𝔞 s₁ - 𝔞 s₀ := by linear_combination -eds
    have hdc : 𝔞 (monus c₀ c₁) = 𝔞 c₀ - 𝔞 c₁ := by linear_combination -edc
    have X := cell_ring (𝔞 M₀ + 1) (𝔞 𝔉) ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * (𝔞 j + 1))
      ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) (𝔞 j) (𝔞 s₀) (𝔞 s₁) (𝔞 c₀) (𝔞 c₁) (𝔞 ω₀) (𝔞 i)
      (𝔞 (pw s₀ i)) (𝔞 (pw s₀ (succ i))) (𝔞 (pw s₀ (succ (succ i)))) (𝔞 (pw s₁ (succ i)))
      (𝔞 (gd s₁ s₀ (succ i))) (𝔞 (kd s₁ s₀ i)) (by ring) (by linear_combination r1)
      (by linear_combination r2) (by linear_combination r3) (by linear_combination r4)
      (by linear_combination r5) (by linear_combination r6)
    rw [hds, hdc, f3, f2, f1]
    generalize (𝔞 M₀ + 1) = Mv at X ⊢
    generalize Mv * Mv + 𝔞 j * 𝔞 j = Dv at X ⊢
    linear_combination (2 * Mv) * X

end cell

/-! ## The sums -/

/-- `om_j sg_j^k` over `(j, k, M, L)`; `𝒥_k = ∑_{j<M} om_j sg_j^k = M F^{k+1} J_k(M)`. -/
abbrev Jb : PTm 2 := lift4 (om (var 0) (var 2) (var 3) * pw (sg (var 0) (var 2) (var 3)) (var 1))
abbrev J (k M L : PTm n) : PTm n := ap2 (sumF Jb) M (pairT k (pairT M L))

/-- `om_j (i + 1) gm_j² sg_j^i` over `(j, i, M, L)`. -/
abbrev HpB : PTm 2 := lift4 (om (var 0) (var 2) (var 3) *
  (succ (var 1) * (gm (var 0) (var 2) (var 3) * gm (var 0) (var 2) (var 3)) * pw (sg (var 0) (var 2) (var 3)) (var 1)))

/-- `(i + 1) F² om_j sg_j^i` over `(j, i, M, L)`. -/
abbrev KB : PTm 2 := lift4 (succ (var 1) * (fact (var 3) * fact (var 3)) *
  (om (var 0) (var 2) (var 3) * pw (sg (var 0) (var 2) (var 3)) (var 1)))

theorem inst_Jb (j k M L : PTm n) :
    Γ ⊢[PRAAx] inst2 Jb j (pairT k (pairT M L)) ≐ om j M L * pw (sg j M L) k := by
  have h := inst2_lift4 (Γ := Γ) (om (var 0) (var 2) (var 3) * pw (sg (var 0) (var 2) (var 3)) (var 1)) j k M L
  simp at h; exact h

theorem inst_HpB (j i M L : PTm n) :
    Γ ⊢[PRAAx] inst2 HpB j (pairT i (pairT M L)) ≐
      om j M L * (succ i * (gm j M L * gm j M L) * pw (sg j M L) i) := by
  have h := inst2_lift4 (Γ := Γ) (om (var 0) (var 2) (var 3) *
    (succ (var 1) * (gm (var 0) (var 2) (var 3) * gm (var 0) (var 2) (var 3)) * pw (sg (var 0) (var 2) (var 3)) (var 1)))
    j i M L
  simp at h; exact h

theorem inst_KB (j i M L : PTm n) :
    Γ ⊢[PRAAx] inst2 KB j (pairT i (pairT M L)) ≐
      succ i * (fact L * fact L) * (om j M L * pw (sg j M L) i) := by
  have h := inst2_lift4 (Γ := Γ) (succ (var 1) * (fact (var 3) * fact (var 3)) *
    (om (var 0) (var 2) (var 3) * pw (sg (var 0) (var 2) (var 3)) (var 1))) j i M L
  simp at h; exact h

/-! ## Summing the cells -/

/-- `G_j = gm_j sg_j^{i+1}`. -/
abbrev Gt (j i M L : PTm n) : PTm n := gm j M L * pw (sg j M L) (succ i)

/-- The partial sums of `cell_up`. -/
abbrev UpInv (j i M₀ L : PTm n) : Fm PTm n :=
  le (succ M₀ * (succ M₀ * fact L * Gt j i (succ M₀) L) +
      succ M₀ * ap2 (sumF Jb) j (pairT (succ (succ i)) (pairT (succ M₀) L)))
    (succ M₀ * (succ M₀ * fact L * Gt zero i (succ M₀) L) +
      succ M₀ * ap2 (sumF HpB) j (pairT i (pairT (succ M₀) L)) +
      j * ((two * (i * succ i) + two) * pw (fact L) (succ (succ (succ i)))))

/-- The partial sums of `cell_dn`. -/
abbrev DnInv (j i M₀ L : PTm n) : Fm PTm n :=
  le (succ M₀ * (succ M₀ * fact L * Gt zero i (succ M₀) L) +
      succ M₀ * ap2 (sumF HpB) j (pairT i (pairT (succ M₀) L)))
    (succ M₀ * (succ M₀ * fact L * Gt j i (succ M₀) L) +
      succ M₀ * ap2 (sumF Jb) j (pairT (succ (succ i)) (pairT (succ M₀) L)) +
      j * ((num 8 * succ i + two) * pw (fact L) (succ (succ (succ i)))))

theorem up_base (i M₀ L : PTm n) : Γ ⊢[PRAAx] UpInv zero i M₀ L := by
  have z1 := natEq (sum_zero (Γ := Γ) Jb (pairT (succ (succ i)) (pairT (succ M₀) L)))
  have z2 := natEq (sum_zero (Γ := Γ) HpB (pairT i (pairT (succ M₀) L)))
  ipra_le 0 using rw [z1, z2]; ring

theorem dn_base (i M₀ L : PTm n) : Γ ⊢[PRAAx] DnInv zero i M₀ L := by
  have z1 := natEq (sum_zero (Γ := Γ) Jb (pairT (succ (succ i)) (pairT (succ M₀) L)))
  have z2 := natEq (sum_zero (Γ := Γ) HpB (pairT i (pairT (succ M₀) L)))
  ipra_le 0 using rw [z1, z2]; ring

theorem up_step {j i M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (ih : Γ ⊢[PRAAx] UpInv j i M₀ L) :
    Γ ⊢[PRAAx] UpInv (succ j) i M₀ L := by
  have c := cell_up (i := i) hj hL
  have e1 := natEq (sum_succ' (Γ := Γ) Jb j (pairT (succ (succ i)) (pairT (succ M₀) L)))
  have e2 := natEq (inst_Jb (Γ := Γ) j (succ (succ i)) (succ M₀) L)
  have e3 := natEq (sum_succ' (Γ := Γ) HpB j (pairT i (pairT (succ M₀) L)))
  have e4 := natEq (inst_HpB (Γ := Γ) j i (succ M₀) L)
  ipra_le sl ih + sl c using rw [e1, e2, e3, e4]; ring

theorem dn_step {j i M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (ih : Γ ⊢[PRAAx] DnInv j i M₀ L) :
    Γ ⊢[PRAAx] DnInv (succ j) i M₀ L := by
  have c := cell_dn (i := i) hj hL
  have e1 := natEq (sum_succ' (Γ := Γ) Jb j (pairT (succ (succ i)) (pairT (succ M₀) L)))
  have e2 := natEq (inst_Jb (Γ := Γ) j (succ (succ i)) (succ M₀) L)
  have e3 := natEq (sum_succ' (Γ := Γ) HpB j (pairT i (pairT (succ M₀) L)))
  have e4 := natEq (inst_HpB (Γ := Γ) j i (succ M₀) L)
  ipra_le sl ih + sl c using rw [e1, e2, e3, e4]; ring

/-- Variables: `0 = j` (induction), `1 = i`, `2 = M₀`, `3 = L`. -/
private abbrev upF : Fm PTm 4 :=
  le (two * (succ (var 2) * succ (var 2))) (var 3) ⟶ le (var 0) (succ (var 2)) ⟶
    UpInv (var 0) (var 1) (var 2) (var 3)

private abbrev dnF : Fm PTm 4 :=
  le (two * (succ (var 2) * succ (var 2))) (var 3) ⟶ le (var 0) (succ (var 2)) ⟶
    DnInv (var 0) (var 1) (var 2) (var 3)

private theorem up₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] upF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      subst_sg, subst_gm, subst_om, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, inst_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (up_base _ _ _))
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      subst_sg, subst_gm, subst_om, Syn.subst_var, Syn.repl_zero, repl_one, repl_two, repl_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (up_step Prf.hyp1 Prf.hyp0
      (Prf.impE (Prf.impE Prf.hyp1.wk Prf.hyp1) (le_trans (le_succ_self _) Prf.hyp0))))

private theorem dn₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] dnF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      subst_sg, subst_gm, subst_om, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, inst_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (dn_base _ _ _))
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      subst_sg, subst_gm, subst_om, Syn.subst_var, Syn.repl_zero, repl_one, repl_two, repl_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (dn_step Prf.hyp1 Prf.hyp0
      (Prf.impE (Prf.impE Prf.hyp1.wk Prf.hyp1) (le_trans (le_succ_self _) Prf.hyp0))))

theorem up_all {j i M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (hj : Γ ⊢[PRAAx] le j (succ M₀)) : Γ ⊢[PRAAx] UpInv j i M₀ L := by
  have h := inst (Γ := Γ) up₀ (![j, i, M₀, L] : Fin 4 → PTm n)
  simp at h
  exact Prf.impE (Prf.impE h hL) hj

theorem dn_all {j i M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (hj : Γ ⊢[PRAAx] le j (succ M₀)) : Γ ⊢[PRAAx] DnInv j i M₀ L := by
  have h := inst (Γ := Γ) dn₀ (![j, i, M₀, L] : Fin 4 → PTm n)
  simp at h
  exact Prf.impE (Prf.impE h hL) hj

/-! ## The recurrence -/

/-- `∑_{j<M} H⁺_j + (i + 1) 𝒥_{i+2} = (i + 1) F² 𝒥_i`, by `c² + s² = 1` at each grid point. -/
theorem Hp_sum {i M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] ap2 (sumF HpB) (succ M₀) (pairT i (pairT (succ M₀) L)) +
        succ i * J (succ (succ i)) (succ M₀) L ≐ succ i * (fact L * fact L) * J i (succ M₀) L := by
  have hLs := (LeanProofs.IPRA.Analysis.BaselAverages.shift_le hL).wk (ψ := lt (var 0) (Syn.shift (succ M₀)))
  have es2 : Syn.shift (two * (succ M₀ * succ M₀)) = two * (succ (Syn.shift M₀) * succ (Syn.shift M₀)) := by
    simp [Syn.shift]
  have es1 : Syn.shift (succ M₀) = succ (Syn.shift M₀) := by simp [Syn.shift]
  have esi : Syn.shift (succ i) = succ (Syn.shift i) := by simp [Syn.shift]
  have esii : Syn.shift (succ (succ i)) = succ (succ (Syn.shift i)) := by simp [Syn.shift]
  rw [es2, es1] at hLs
  have a := sum_lin (Γ := Γ) HpB Jb KB (succ M₀) (pairT i (pairT (succ M₀) L))
    (pairT (succ (succ i)) (pairT (succ M₀) L)) (pairT i (pairT (succ M₀) L)) (succ i) (.allI (.impI (by
      simp only [shift_pairT, es1, esi, esii]
      have hj : (lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (succ (Syn.shift M₀)) :=
        le_trans (le_succ_self _) Prf.hyp0
      have py := natEq (pyth hj hLs)
      have i1 := natEq (inst_HpB (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0)
        (Syn.shift i) (succ (Syn.shift M₀)) (Syn.shift L))
      have i2 := natEq (inst_Jb (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0)
        (succ (succ (Syn.shift i))) (succ (Syn.shift M₀)) (Syn.shift L))
      have i3 := natEq (inst_KB (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) (var 0)
        (Syn.shift i) (succ (Syn.shift M₀)) (Syn.shift L))
      have p2 := natEq (pw_succ (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift)
        (sg (var 0) (succ (Syn.shift M₀)) (Syn.shift L)) (succ (Syn.shift i)))
      have p1 := natEq (pw_succ (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift)
        (sg (var 0) (succ (Syn.shift M₀)) (Syn.shift L)) (Syn.shift i))
      apply deriveNat; ipra_simps
      rw [i1, i2, i3, p2, p1]
      linear_combination ((𝔟 (Syn.shift i) + 1) * 𝔟 (om (var 0) (succ (Syn.shift M₀)) (Syn.shift L)) *
        𝔟 (pw (sg (var 0) (succ (Syn.shift M₀)) (Syn.shift L)) (Syn.shift i))) * py)))
  have b := sum_scale (Γ := Γ) KB Jb (succ M₀) (succ i * (fact L * fact L)) (pairT i (pairT (succ M₀) L))
    (pairT i (pairT (succ M₀) L)) (.allI (.impI (by
      simp only [shift_pairT, es1]
      have e : Syn.shift (succ i * (fact L * fact L)) =
          succ (Syn.shift i) * (fact (Syn.shift L) * fact (Syn.shift L)) := by simp [Syn.shift]
      rw [e]
      exact (inst_KB _ _ _ _).eqTrans (congrMul (.eqRefl _) (inst_Jb _ _ _ _).eqSymm))))
  exact a.eqTrans b

/-- `eq:Jrec` for `k = i + 2`, cleared by `F = L!` with `2M² ≤ L` (`M = M₀ + 1`):
`(i + 2) 𝒥_{i+2} ≤ (i + 1) F² 𝒥_i + (2i(i+1) + 2) F^{i+3}` and
`(i + 1) F² 𝒥_i ≤ (i + 2) 𝒥_{i+2} + (8(i+1) + 2) F^{i+3}`, i.e.
`−(8k − 6)/M ≤ (k − 1) J_{k−2}(M) − k J_k(M) ≤ (2k² − 6k + 6)/M`. -/
theorem wallis_rec {i M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (succ (succ i) * J (succ (succ i)) (succ M₀) L)
        (succ i * (fact L * fact L) * J i (succ M₀) L +
          (two * (i * succ i) + two) * pw (fact L) (succ (succ (succ i)))) ⋏
      le (succ i * (fact L * fact L) * J i (succ M₀) L)
        (succ (succ i) * J (succ (succ i)) (succ M₀) L +
          (num 8 * succ i + two) * pw (fact L) (succ (succ (succ i)))) := by
  have u := up_all (i := i) hL (le_refl (succ M₀))
  have d := dn_all (i := i) hL (le_refl (succ M₀))
  have hs := natEq (Hp_sum (i := i) hL)
  have gt := natEq (gm_top (Γ := Γ) (succ M₀) L)
  have s0 := natEq (sg_zero (Γ := Γ) (succ M₀) L)
  have ps := natEq (pw_succ (Γ := Γ) (sg zero (succ M₀) L) i)
  refine .andI (mul_le_cancel (d' := M₀) ?_) (mul_le_cancel (d' := M₀) ?_)
  · ipra_le sl u using
      rw [gt, ps, s0]
      linear_combination (-(𝔞 M₀ + 1)) * hs
  · ipra_le sl d using
      rw [gt, ps, s0]
      linear_combination (𝔞 M₀ + 1) * hs

/-- `eq:Jrec` with the constant of the paper: `|(k − 1) F² 𝒥_{k−2} − k 𝒥_k| ≤ 8k² F^{k+1}` for `k = i + 2`. -/
theorem wallis_rec_paper {i M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (succ (succ i) * J (succ (succ i)) (succ M₀) L)
        (succ i * (fact L * fact L) * J i (succ M₀) L +
          num 8 * (succ (succ i) * succ (succ i)) * pw (fact L) (succ (succ (succ i)))) ⋏
      le (succ i * (fact L * fact L) * J i (succ M₀) L)
        (succ (succ i) * J (succ (succ i)) (succ M₀) L +
          num 8 * (succ (succ i) * succ (succ i)) * pw (fact L) (succ (succ (succ i)))) := by
  have r := wallis_rec (i := i) hL
  have r1 := Prf.andE₁ r; have r2 := Prf.andE₂ r
  refine .andI ?_ ?_
  · ipra_le sl r1 + (6 * (𝔞 i * 𝔞 i) + 30 * 𝔞 i + 30) * 𝔞 (pw (fact L) (succ (succ (succ i))))
  · ipra_le sl r2 + (8 * (𝔞 i * 𝔞 i) + 24 * 𝔞 i + 22) * 𝔞 (pw (fact L) (succ (succ (succ i))))

end LeanProofs.IPRA.Analysis.WallisRecurrence
