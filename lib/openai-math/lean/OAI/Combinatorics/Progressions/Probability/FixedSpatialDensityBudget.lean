import OAI.Combinatorics.Progressions.Linear.AllocatedKernelSlowBudget

namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem factorial_le_exp_square (n : ℕ) {P : ℝ} (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) :
    (n.factorial : ℝ) ≤ Real.exp (P ^ 2) := by
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
  have hbase : (n : ℝ) ≤ Real.exp P := hn.trans (le_trans (by linarith) (Real.add_one_le_exp P))
  calc
    _ ≤ (n : ℝ) ^ n := hfac
    _ ≤ (Real.exp P) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = Real.exp (P * n) := by simpa only [mul_comm] using (Real.exp_nat_mul P n).symm
    _ ≤ Real.exp (P ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

theorem fixedSpatialDensityLipschitz_exp_budget (n : ℕ) {P B H κ0 κ1 : ℝ}
    (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) (hH : 0 ≤ H) (hH1 : H ≤ 1)
    (hκ0 : 0 < κ0) (hκ1 : 0 < κ1)
    (hi0 : κ0⁻¹ ≤ Real.exp B) (hi1 : κ1⁻¹ ≤ Real.exp B) :
    2 * (n : ℝ) * κ1⁻¹ * (n * (n.factorial * H ^ (n - 1) / κ0)) ≤
      Real.exp (2 * B + P ^ 2 + 2 * P + 2) := by
  have hfac := factorial_le_exp_square n hP hn
  have hp : H ^ (n - 1) ≤ 1 := pow_le_one₀ hH hH1
  have hnexp : (n : ℝ) ≤ Real.exp P := hn.trans
    (le_trans (by linarith) (Real.add_one_le_exp P))
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  have hinner : (n.factorial : ℝ) * H ^ (n - 1) / κ0 ≤ Real.exp (P ^ 2) * Real.exp B := by
    rw [div_eq_mul_inv]
    apply mul_le_mul _ hi0 (inv_nonneg.mpr hκ0.le) (Real.exp_nonneg _)
    exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)).trans (by simpa using hfac)
  calc
    _ ≤ (Real.exp 2 * Real.exp P) * Real.exp B *
        (Real.exp P * (Real.exp (P ^ 2) * Real.exp B)) := by
      apply mul_le_mul
      · exact mul_le_mul (mul_le_mul h2 hnexp (Nat.cast_nonneg _) (Real.exp_nonneg _)) hi1
          (inv_nonneg.mpr hκ1.le) (by positivity)
      · exact mul_le_mul hnexp hinner (by positivity) (Real.exp_nonneg _)
      · positivity
      · positivity
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
