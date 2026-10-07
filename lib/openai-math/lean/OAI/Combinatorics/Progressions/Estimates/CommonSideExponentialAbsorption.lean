import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem commonSide_exp_absorption (n E : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((n : ℝ) + 1) * Real.exp ((t + 2) ^ E) ≤
      Real.exp ((t + 2) ^ (E + n + 3)) := by
  have hbase : (1 : ℝ) ≤ t + 2 := by linarith
  have hpower : (1 : ℝ) ≤ (t + 2) ^ E := one_le_pow₀ hbase
  have hlinear : (n : ℝ) + 2 ≤ (t + 2) ^ (n + 1) := by
    calc
      (n : ℝ) + 2 ≤ (2 : ℝ) ^ (n + 1) := by
        have h := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1) (n + 1)
        norm_num only [Nat.cast_add, Nat.cast_one, mul_one, one_add_one_eq_two] at h
        linarith
      _ ≤ (t + 2) ^ (n + 1) := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hexponent : (n : ℝ) + (t + 2) ^ E ≤ (t + 2) ^ (E + n + 3) := by
    calc
      (n : ℝ) + (t + 2) ^ E ≤ ((n : ℝ) + 2) * (t + 2) ^ E := by
        nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hpower)]
      _ ≤ (t + 2) ^ (n + 1) * (t + 2) ^ E :=
        mul_le_mul_of_nonneg_right hlinear (by positivity)
      _ = (t + 2) ^ (E + n + 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ (t + 2) ^ (E + n + 3) := pow_le_pow_right₀ hbase (by omega)
  calc
    ((n : ℝ) + 1) * Real.exp ((t + 2) ^ E) ≤
        Real.exp (n : ℝ) * Real.exp ((t + 2) ^ E) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp (n : ℝ)) (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) + (t + 2) ^ E) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((t + 2) ^ (E + n + 3)) := Real.exp_le_exp.mpr hexponent

end Erdos3

end

end OAI
