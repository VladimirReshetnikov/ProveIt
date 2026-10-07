import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem nat_monomial_root_le (n C L : ℕ) (hn : 0 < n) (hC : 1 ≤ C) :
    ((C * L ^ n : ℕ) : ℝ) ^ (1 / (n : ℝ)) ≤ (C : ℝ) * L := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : C * L ^ n ≤ (C * L) ^ n := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ (le_self_pow hC hn.ne')
  calc
    _ ≤ (((C * L : ℕ) : ℝ) ^ n) ^ (1 / (n : ℝ)) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by positivity)
      exact_mod_cast hpow
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
        mul_one_div_cancel hn', Real.rpow_one, Nat.cast_mul]

end Erdos3

end

end OAI
