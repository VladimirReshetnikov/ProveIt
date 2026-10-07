import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem complex_normalization_error {M F : ℂ} {Z E ε D : ℝ}
    (hZ : 1 / 2 ≤ Z) (herror : ‖M - F‖ ≤ E)
    (hmass : |Z - 1| ≤ ε) (hcap : ‖F‖ ≤ D) :
    ‖M / (Z : ℂ) - F‖ ≤ 2 * E + 2 * D * ε := by
  have hZpos : 0 < Z := by linarith
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZpos.ne'
  have hE : 0 ≤ E := (norm_nonneg _).trans herror
  have hε : 0 ≤ ε := (abs_nonneg _).trans hmass
  have hD : 0 ≤ D := (norm_nonneg _).trans hcap
  have he : M / (Z : ℂ) - F = ((M - F) + F * (1 - (Z : ℂ))) / (Z : ℂ) := by
    field_simp
    ring
  rw [he, norm_div, Complex.norm_real, Real.norm_of_nonneg hZpos.le]
  have hz : ‖1 - (Z : ℂ)‖ ≤ ε := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [abs_sub_comm] using hmass
  have hn : ‖(M - F) + F * (1 - (Z : ℂ))‖ ≤ E + D * ε :=
    (norm_add_le _ _).trans (add_le_add herror (by
      rw [norm_mul]
      exact mul_le_mul hcap hz (norm_nonneg _) hD))
  calc
    _ ≤ (E + D * ε) / Z := div_le_div_of_nonneg_right hn hZpos.le
    _ ≤ 2 * E + 2 * D * ε := (div_le_iff₀ hZpos).mpr (by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * Z - 1) (by positivity : 0 ≤ E + D * ε)])

end Erdos3

end

end OAI
