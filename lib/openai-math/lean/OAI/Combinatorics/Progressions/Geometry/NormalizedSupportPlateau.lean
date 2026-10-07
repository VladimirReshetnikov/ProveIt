import Mathlib.Analysis.Normed.Group.Basic
import OAI.Combinatorics.Progressions.Estimates.LinearCutoff

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {J : Type*} [Fintype J]

noncomputable def normalizedSupportPlateau (H : ℝ) (x : J → ℝ) : ℝ :=
  linearCutoff H (1 / 4) ‖x‖

theorem normalizedSupportPlateau_range (H : ℝ) (x : J → ℝ) :
    0 ≤ normalizedSupportPlateau H x ∧ normalizedSupportPlateau H x ≤ 1 :=
  linearCutoff_range _ _ _

theorem normalizedSupportPlateau_one {H : ℝ} (hH : 0 ≤ H) (x : J → ℝ)
    (hx : ∀ j, |x j| ≤ H) : normalizedSupportPlateau H x = 1 := by
  apply linearCutoff_eq_one _ _ (by norm_num)
  exact (pi_norm_le_iff_of_nonneg hH).mpr (by simpa only [Real.norm_eq_abs] using hx)

theorem normalizedSupportPlateau_support {H : ℝ} (x : J → ℝ)
    (hx : normalizedSupportPlateau H x ≠ 0) : ∀ j, |x j| < H + 1 / 4 := by
  have hn : ‖x‖ < H + 1 / 4 := by
    apply lt_of_not_ge
    intro h
    apply hx
    exact linearCutoff_eq_zero H (1 / 4) (by simpa using h)
  intro j
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  exact hj.trans_lt hn

theorem normalizedSupportPlateau_lipschitz (H : ℝ) :
    LipschitzWith 4 (normalizedSupportPlateau (J := J) H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (linearCutoff_lipschitz H (1 / 4) (by norm_num)).dist_le_mul ‖x‖ ‖y‖
  norm_num only [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    one_div, inv_inv] at h
  exact h.trans (mul_le_mul_of_nonneg_left (dist_norm_norm_le x y) (by norm_num))

theorem normalizedSupportPlateau_grid_one {H : ℝ} (hH : 0 ≤ H) {K : ℕ} (hK : 0 < K)
    (center z : J → ℤ) (hz : ∀ j, |(z j : ℝ) - center j| ≤ H * K) :
    normalizedSupportPlateau H (fun j => ((z j : ℝ) - center j) / K) = 1 := by
  apply normalizedSupportPlateau_one hH
  intro j
  rw [abs_div, abs_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)]
  exact (div_le_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mpr (hz j)

theorem normalizedSupportPlateau_grid_support {H : ℝ} {K : ℕ} (hK : 0 < K)
    (center z : J → ℤ)
    (hz : normalizedSupportPlateau H (fun j => ((z j : ℝ) - center j) / K) ≠ 0) :
    ∀ j, |(z j : ℝ) - center j| ≤ (H + 1 / 4) * K := by
  have h := normalizedSupportPlateau_support _ hz
  intro j
  have hj := h j
  rw [abs_div, abs_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)] at hj
  exact ((div_lt_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mp hj).le

end Erdos3

end

end OAI
