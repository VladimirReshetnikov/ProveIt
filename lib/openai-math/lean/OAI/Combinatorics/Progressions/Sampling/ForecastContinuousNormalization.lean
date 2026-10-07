import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem forecastContinuous_normalized_bounds {Y : Type*} [PseudoMetricSpace Y]
    (density : Y → ℝ) (H : ℝ) (hH : 1 ≤ H) (hcap : ∀ y, ‖density y‖ ≤ H)
    (LG : ℝ≥0) (hLG : LipschitzWith LG density) :
    (∀ y, ‖(density y : ℂ) / (H : ℂ)‖ ≤ 1) ∧
      LipschitzWith LG (fun y => (density y : ℂ) / (H : ℂ)) ∧
      ∀ y, (density y : ℂ) = (H : ℂ) * ((density y : ℂ) / (H : ℂ)) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHne : (H : ℂ) ≠ 0 := by exact_mod_cast hHpos.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hHpos.le]
    exact (div_le_one hHpos).mpr (hcap y)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← sub_div, ← Complex.ofReal_sub, norm_div,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hHpos.le]
    exact (div_le_self (norm_nonneg _) hH).trans
      (by simpa only [dist_eq_norm] using hLG.dist_le_mul x y)
  · intro y
    exact (mul_div_cancel₀ (density y : ℂ) hHne).symm

theorem forecastContinuous_scaled_error {Y : Type*}
    (density : Y → ℝ) (H : ℝ) (hH : 1 ≤ H) (hcap : ∀ y, ‖density y‖ ≤ H)
    (y : Y) {target model : ℂ} {ε : ℝ} (happrox : ‖target - model‖ ≤ ε) :
    ‖(density y : ℂ) * target - (density y : ℂ) * model‖ ≤ H * ε := by
  rw [← mul_sub, norm_mul, Complex.norm_real]
  exact mul_le_mul (hcap y) happrox (norm_nonneg _) (zero_le_one.trans hH)

end Erdos3

end

end OAI
