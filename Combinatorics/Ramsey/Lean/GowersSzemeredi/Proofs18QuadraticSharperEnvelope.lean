import GowersSzemeredi.Proofs18QuadraticNumericalConstant
import GowersSzemeredi.Proofs18DensityIterationExponentialBudget
import GowersSzemeredi.Proofs18LogarithmicPowerEnvelope

/-! Logarithmic estimates for the unchanged four-term density iteration.
The fixed refinement constant and the inverse length exponent are bounded
before assembling the outer double exponential. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The large fixed constant contributes only degree 324 to the logarithm
of the iteration budget. -/
theorem quadratic_iteration_log_budget_le_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    1 + Real.log (max 1 (intervalQuadraticStepThreshold delta)) +
        |Real.log (intervalQuadraticLengthFactor delta)| ≤
      Real.exp ((2 / intervalQuadraticUniformityParameter delta) ^ (324 : Nat)) := by
  let x := 2 / intervalQuadraticUniformityParameter delta
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hαone := intervalQuadraticUniformityParameter_le_one hδ.le hδone
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hC : quadraticIterationLogBudgetConstant ≤ Real.exp (x ^ (323 : Nat)) := by
    apply (le_add_of_nonneg_right (by norm_num : (0 : Real) ≤ 1)).trans
    exact quadraticIterationLogBudgetConstant_upper.trans
      ((pow_le_pow_left₀ (by norm_num) hx _).trans (pow_two_pow_le_exp_pow_succ hx 322))
  have hP : x ^ (25378984 : Nat) ≤ Real.exp (x ^ (26 : Nat)) :=
    (pow_le_pow_right₀ hx1 (by norm_num : (25378984 : Nat) ≤ 2 ^ 25)).trans
      (pow_two_pow_le_exp_pow_succ hx 25)
  have hsum : x ^ (323 : Nat) + x ^ (26 : Nat) ≤ x ^ (324 : Nat) := by
    calc
      _ ≤ 2 * x ^ (323 : Nat) := by
        have h := pow_le_pow_right₀ hx1 (by norm_num : (26 : Nat) ≤ 323)
        linarith only [h]
      _ ≤ x * x ^ (323 : Nat) := mul_le_mul_of_nonneg_right hx (by positivity)
      _ = _ := (pow_succ' x 323).symm
  apply (quadratic_iteration_log_budget hδ hδone).trans
  calc
    _ ≤ Real.exp (x ^ (323 : Nat)) * Real.exp (x ^ (26 : Nat)) :=
      mul_le_mul hC hP (by positivity) (by positivity)
    _ = Real.exp (x ^ (323 : Nat) + x ^ (26 : Nat)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hsum

/-- Taking the logarithm of the inverse length exponent keeps the density
iteration exponent small; no source threshold is changed. -/
theorem quadraticIntervalClosedThreshold_le_double_exp_alpha_sharp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    quadraticIntervalClosedThreshold delta ≤
      Real.exp (Real.exp ((2 / intervalQuadraticUniformityParameter delta) ^ (12402 : Nat))) := by
  let x := 2 / intervalQuadraticUniformityParameter delta
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hαone := intervalQuadraticUniformityParameter_le_one hδ.le hδone
  have hx : 2 ≤ x := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hx1 : 1 ≤ x := by linarith only [hx]
  obtain ⟨_, hg, hr, _⟩ := quadratic_interval_parameters_inv_upper hα hαone
  have hb : 2 * max 1 (quadraticDiscrepancyExponent (intervalQuadraticUniformityParameter delta) / 16)⁻¹ ≤
      Real.exp (x ^ (16 : Nat)) := by
    calc
      _ ≤ x * x ^ (24748 : Nat) :=
        mul_le_mul hx (max_le (one_le_pow₀ hx1) hr)
          (le_trans (by norm_num) (le_max_left _ _)) (by linarith only [hx])
      _ = x ^ (24749 : Nat) := (pow_succ' x 24748).symm
      _ ≤ x ^ ((2 : Nat) ^ 15) := pow_le_pow_right₀ hx1 (by norm_num)
      _ ≤ _ := pow_two_pow_le_exp_pow_succ hx 15
  have hA := (quadratic_iteration_log_budget_le_exp hδ hδone).trans
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ hx1 (by norm_num : (324 : Nat) ≤ 12401)))
  exact densityIterationClosedThreshold_le_double_exp_of_exp_budget _ _ _ _ _
    12384 16 12401 (intervalQuadratic_constants_pos hδ).1 hx hA hg hb (by norm_num)

/-- An explicit double-exponential envelope in the initial density, with
no unspecified fixed prefactor. -/
theorem quadraticIntervalClosedThreshold_le_double_exp_sharp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    quadraticIntervalClosedThreshold delta ≤
      Real.exp (Real.exp ((2 / delta) ^ (1500642 : Nat))) := by
  have hα := intervalQuadraticUniformityParameter_pos hδ
  apply (quadraticIntervalClosedThreshold_le_double_exp_alpha_sharp hδ hδone).trans
  apply Real.exp_le_exp.mpr (Real.exp_le_exp.mpr _)
  have h := pow_le_pow_left₀
    (by positivity : 0 ≤ 2 / intervalQuadraticUniformityParameter delta)
    (intervalQuadraticUniformityParameter_inv_upper hδ hδone).2 (12402 : Nat)
  simpa only [← pow_mul] using h

/-- In the half-density range, absorb the fixed factor 2^121 directly
into the reciprocal density instead of squaring the coarser 2/delta bound. -/
theorem two_div_intervalQuadraticUniformityParameter_le_inv_pow {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    2 / intervalQuadraticUniformityParameter delta ≤ delta⁻¹ ^ (153 : Nat) := by
  have hu : 2 ≤ delta⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hδ).mpr
    linarith only [hδhalf]
  have heq : 2 / intervalQuadraticUniformityParameter delta =
      (2 : Real) ^ (121 : Nat) * delta⁻¹ ^ (32 : Nat) := by
    unfold intervalQuadraticUniformityParameter
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, ← inv_pow, mul_pow, ← pow_mul]
    norm_num
    ring
  rw [heq]
  calc
    _ ≤ delta⁻¹ ^ (121 : Nat) * delta⁻¹ ^ (32 : Nat) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hu _) (by positivity)
    _ = _ := (pow_add _ 121 32).symm

end LeanProofs.GowersSzemeredi
