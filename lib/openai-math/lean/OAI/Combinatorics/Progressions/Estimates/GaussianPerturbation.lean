import Mathlib

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_sq_le_four_add_dilated_norm_sq (x y : E) {ε : ℝ}
    (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hxy : ‖x - y‖ ≤ ε) :
    ‖x‖ ^ 2 ≤ 4 + ‖(1 + ε) • y‖ ^ 2 := by
  have hnorm : ‖x‖ ≤ ε + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ ε + ‖y‖ := add_le_add hxy le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + ε)]
  by_cases hx : ‖x‖ ≤ 2
  · nlinarith [norm_nonneg x, sq_nonneg ((1 + ε) * ‖y‖)]
  · have hlarge : 2 < ‖x‖ := lt_of_not_ge hx
    have hc : 0 ≤ ε * (‖x‖ - 1 - ε) := mul_nonneg hε (by linarith)
    have hm := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 1 + ε by linarith)
    have hbound : ‖x‖ ≤ (1 + ε) * ‖y‖ := by nlinarith only [hc, hm]
    nlinarith only [hbound, sq_nonneg ((1 + ε) * ‖y‖ - ‖x‖), norm_nonneg x]

theorem gaussian_perturbation_lower (x y : E) {ε : ℝ}
    (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hxy : ‖x - y‖ ≤ ε) :
    Real.exp (-4 * Real.pi) * Real.exp (-Real.pi * ‖(1 + ε) • y‖ ^ 2) ≤
      Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left (norm_sq_le_four_add_dilated_norm_sq x y hε hεone hxy)
    Real.pi_pos.le
  nlinarith only [hm]

theorem gaussian_orbit_perturbation_lower (α β m : E) {N k : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hclose : (N : ℝ) ^ k * ‖α - β‖ ≤ ε)
    (n : ℤ) (hn : |n| ≤ (N : ℤ)) :
    Real.exp (-4 * Real.pi) *
        Real.exp (-Real.pi * ‖(1 + ε) • ((n : ℝ) ^ k • β - m)‖ ^ 2) ≤
      Real.exp (-Real.pi * ‖(n : ℝ) ^ k • α - m‖ ^ 2) := by
  apply gaussian_perturbation_lower _ _ hε hεone
  have hid : ((n : ℝ) ^ k • α - m) - ((n : ℝ) ^ k • β - m) =
      (n : ℝ) ^ k • (α - β) := by module
  rw [hid, norm_smul, Real.norm_eq_abs, abs_pow]
  have hnR : |(n : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hn
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hnR k) (norm_nonneg _)).trans hclose

end Erdos3

end

end OAI
