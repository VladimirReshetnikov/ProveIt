import GowersSzemeredi.Proofs18DensityIterationPowerBound
import GowersSzemeredi.Proofs18QuadraticIterationParameters
import GowersSzemeredi.Proofs18QuadraticClosedBound

/-! This module keeps `quadraticIterationLogBudgetConstant` and
`quadratic_iteration_log_budget`; the rest of the development, with its
description, is in `Proofs18QuadraticDoubleExponentialSide`, outside the final
route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def quadraticIterationLogBudgetConstant : Real :=
  (4 + 6 * section5LocalRefinementConstant 2 1) + 8230 + 8 * section5LocalRefinementConstant 1 1

theorem quadratic_iteration_log_budget {delta : Real} (hδ : 0 < delta) (hδone : delta ≤ 1) :
    1 + Real.log (max 1 (intervalQuadraticStepThreshold delta)) +
        |Real.log (intervalQuadraticLengthFactor delta)| ≤
      quadraticIterationLogBudgetConstant *
        (2 / intervalQuadraticUniformityParameter delta) ^ (25378984 : Nat) := by
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hαone := intervalQuadraticUniformityParameter_le_one hδ.le hδone
  obtain ⟨hτ, -, -, hc⟩ := quadratic_interval_parameters_inv_upper hα hαone
  have hcpos := (intervalQuadratic_constants_pos hδ).2.2
  have hcone := quadratic_interval_length_factor_le_one hα hαone
  have hu : 1 ≤ 2 / intervalQuadraticUniformityParameter delta :=
    (le_div_iff₀ hα).mpr (by linarith)
  have hd4 : (delta ^ 4)⁻¹ ≤ 2 / intervalQuadraticUniformityParameter delta := by
    rw [← inv_div]
    exact inv_anti₀ (by positivity)
      (by linarith [intervalQuadraticUniformityParameter_le_pow_four hδ.le hδone])
  have hS := section5LocalRefinementConstant_pos 2 1
  have hC := section5LocalRefinementConstant_pos 1 1
  unfold quadraticIterationLogBudgetConstant intervalQuadraticStepThreshold
    quadraticExponentialThreshold
  -- opaque `u = 2/α` and `P = u^25378984`, so that no tactic expands the power
  generalize 2 / intervalQuadraticUniformityParameter delta = u at hu hd4 hτ hc ⊢
  have hpow (n : Nat) (hn : n ≤ 25378984) : u ^ n ≤ u ^ 25378984 := pow_le_pow_right₀ hu hn
  have hP : 1 ≤ u ^ 25378984 := one_le_pow₀ hu
  generalize u ^ (25378984 : Nat) = P at hpow hP ⊢
  have hSP := mul_nonneg hS.le (zero_le_one.trans hP)
  have hE := Real.add_one_le_exp ((8233 + 6 * section5LocalRefinementConstant 2 1) * P)
  calc _ ≤ 1 + (8233 + 6 * section5LocalRefinementConstant 2 1) * P +
        8 * section5LocalRefinementConstant 1 1 * P := by
        gcongr 1 + ?_ + ?_
        · refine (Real.log_le_iff_le_exp (by positivity)).mpr (max_le (by linarith)
            (max_le (by linarith) (max_le (Real.exp_le_exp.mpr ?_) (max_le ?_ ?_))))
          · exact mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hP)
          · rw [div_eq_mul_inv]; linarith [hτ.trans (hpow 12381 (by norm_num))]
          · rw [div_eq_mul_inv]; linarith [hpow 1 (by norm_num)]
        · rw [abs_of_nonpos (Real.log_nonpos hcpos.le hcone), ← Real.log_inv]
          exact (Real.log_le_self (inv_nonneg.mpr hcpos.le)).trans (hc.trans
            (mul_le_mul_of_nonneg_left (hpow _ (by norm_num)) (mul_pos (by norm_num) hC).le))
    _ ≤ _ := by linarith

end LeanProofs.GowersSzemeredi
