import OAI.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget

namespace OAI

section

namespace Erdos3

theorem frequency_projection_error_bound {p v M : ℝ} (hp : 0 ≤ p)
    (hM : M ≤ Real.exp v) :
    2 * Real.exp p * Real.exp (-(2 * p + 8)) + M * Real.exp (-(p + v + 8)) ≤
      Real.exp (-p) / 2 := by
  have parameterNonneg := hp
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hinv : Real.exp (-8 : ℝ) ≤ 1 / 8 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) h8
  have hfirst : 2 * Real.exp p * Real.exp (-(2 * p + 8)) =
      2 * Real.exp (-p) * Real.exp (-8) := by
    rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hsecond : Real.exp v * Real.exp (-(p + v + 8)) = Real.exp (-p) * Real.exp (-8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hbound := mul_le_mul_of_nonneg_right hM (Real.exp_nonneg (-(p + v + 8)))
  rw [hsecond] at hbound
  rw [hfirst]
  have hsmall := mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg (-p))
  linarith [parameterNonneg, Real.exp_pos (-p)]

theorem frequency_code_count_bound {p v : ℝ} {D M : ℕ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hD : (D : ℝ) ≤ p) (hM : (M : ℝ) ≤ Real.exp v) :
    ((M : ℝ) + 1) ^ D ≤ Real.exp (p * (v + 1)) := by
  have parameterNonneg := hp
  have hbase : (M : ℝ) + 1 ≤ Real.exp (v + 1) := by
    simpa only [add_zero] using add_le_exp_add_one hv (le_refl (0 : ℝ)) hM
      (by simp : (1 : ℝ) ≤ Real.exp 0)
  calc
    _ ≤ (Real.exp (v + 1)) ^ D := pow_le_pow_left₀ (by positivity) hbase D
    _ = Real.exp ((D : ℝ) * (v + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hD (by linarith [parameterNonneg]))

theorem mass_div_frequency_count {mass p v R : ℝ} {D M : ℕ}
    (hmass : 0 ≤ mass) (hp : 0 ≤ p) (hv : 0 ≤ v) (hD : (D : ℝ) ≤ p)
    (hM : (M : ℝ) ≤ Real.exp v) (hR : p * (v + 1) ≤ R) :
    mass * Real.exp (-R) ≤ mass / ((M : ℝ) + 1) ^ D := by
  have hden := (frequency_code_count_bound hp hv hD hM).trans (Real.exp_le_exp.mpr hR)
  have hi : Real.exp (-R) ≤ 1 / ((M : ℝ) + 1) ^ D := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hden
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hi hmass

end Erdos3

end

end OAI
