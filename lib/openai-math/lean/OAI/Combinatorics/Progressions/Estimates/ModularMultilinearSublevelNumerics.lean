import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem modularSublevel_half_depth {a : ℕ} (ha : 0 < a) :
    0 < (a + 1) / 2 ∧ (a + 1) / 2 ≤ a ∧
      (a : ℝ) / 2 ≤ ((a + 1) / 2 : ℕ) ∧
      (((a + 1) / 2 : ℕ) : ℝ) - 1 - a ≤ -(a : ℝ) / 2 := by
  have h₁ : a ≤ 2 * ((a + 1) / 2) := by omega
  have h₂ : 2 * ((a + 1) / 2) ≤ a + 1 := by omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have : (a : ℝ) ≤ 2 * (((a + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h₁
    linarith
  · have : 2 * (((a + 1) / 2 : ℕ) : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast h₂
    linarith

theorem modularSublevel_fiber_exponent {p : ℝ} (hp : 1 ≤ p) {a : ℕ} (ha : 0 < a) :
    p ^ ((((a + 1) / 2 : ℕ) : ℝ) - 1 - a) ≤ p ^ (-(a : ℝ) / 2) :=
  Real.rpow_le_rpow_of_exponent_le hp (modularSublevel_half_depth ha).2.2.2

theorem modularSublevel_induction_bound {p : ℝ} (hp : 1 ≤ p)
    {a r : ℕ} (ha : 0 < a) (hr : 0 < r) :
    (r : ℝ) * p ^ (-(((a + 1) / 2 : ℕ) : ℝ) / (2 : ℝ) ^ (r - 1)) +
        p ^ (-(a : ℝ) / 2) ≤
      ((r + 1 : ℕ) : ℝ) * p ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  have hpow : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  have hpos : 0 < (2 : ℝ) ^ (r - 1) := by positivity
  have hdepth := (modularSublevel_half_depth ha).2.2.1
  have hexp : -(((a + 1) / 2 : ℕ) : ℝ) / (2 : ℝ) ^ (r - 1) ≤
      -(a : ℝ) / (2 : ℝ) ^ r := by
    rw [hpow]
    apply (div_le_div_iff₀ hpos (by positivity)).2
    nlinarith
  have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc
      (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hexp2 : -(a : ℝ) / 2 ≤ -(a : ℝ) / (2 : ℝ) ^ r := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).2
    nlinarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
  have h₁ := Real.rpow_le_rpow_of_exponent_le hp hexp
  have h₂ := Real.rpow_le_rpow_of_exponent_le hp hexp2
  have h₃ := mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  push_cast
  nlinarith

end Erdos3

end

end OAI
