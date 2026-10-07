import OAI.Combinatorics.Progressions.Estimates.ScalarInitialThreshold

namespace OAI

section

namespace Erdos3

theorem scalarTransfer_doubled_budget (C : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    (2 * p + 2) ^ C ≤ (p + 2) ^ (2 * C) := by
  have hbase : 2 * p + 2 ≤ (p + 2) ^ 2 := by nlinarith
  calc
    _ ≤ ((p + 2) ^ 2) ^ C := pow_le_pow_left₀ (by linarith) hbase C
    _ = _ := (pow_mul _ _ _).symm

theorem scalarTransfer_doubled_log (A : ℕ) (hA : 10 ≤ A) {p : ℝ} (hp : 2 ≤ p) :
    Real.exp ((A : ℝ) * (p + 1)) + 8 ≤ Real.exp ((A : ℝ) * (2 * p + 1)) := by
  have hAr : (10 : ℝ) ≤ A := by exact_mod_cast hA
  have hP : 0 ≤ (A : ℝ) * (p + 1) := by positivity
  have he : 1 ≤ Real.exp ((A : ℝ) * (p + 1)) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hP
  have hdelta : 9 ≤ Real.exp ((A : ℝ) * p) := by
    nlinarith [Real.add_one_le_exp ((A : ℝ) * p)]
  calc
    _ ≤ Real.exp ((A : ℝ) * (p + 1)) * 9 := by nlinarith
    _ ≤ Real.exp ((A : ℝ) * (p + 1)) * Real.exp ((A : ℝ) * p) :=
      mul_le_mul_of_nonneg_left hdelta (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
