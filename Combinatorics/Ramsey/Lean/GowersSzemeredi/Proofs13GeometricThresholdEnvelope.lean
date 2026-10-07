import GowersSzemeredi.Proofs13RecurrenceThresholdEnvelope
import GowersSzemeredi.Proofs13ExplicitGeometricThreshold

/-! A conventional double-exponential bound for the complete Section 13
geometric threshold, including every finite maximum and rounding operation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Every component of the constructed geometric threshold is bounded. -/
theorem section13GeometricThreshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    section13GeometricThreshold delta ≤ Real.exp (Real.exp (112 * section13Q delta)) := by
  have hQ := section13Q_ge_512 hδ hδone
  have hQ0 : 0 ≤ section13Q delta := by linarith only [hQ]
  have hr := section13DensityRecurrenceThreshold_le_double_exp hδ hδone
  have hi := section13DensityIntegerThreshold_le_double_exp hδ hδone
  have hs := section13_square_thresholds_le_spectral_double_exp hδ hδone
  unfold section13GeometricThreshold
  refine max_le (Real.one_le_exp_iff.mpr (Real.exp_pos _).le)
    (max_le (hr.trans ?_) (max_le (hi.trans ?_) hs))
  all_goals exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [hQ0]))

/-- The actual Fejer graph density turns the common spectral double
exponential into an explicit power of the original uniformity parameter. -/
theorem section13_fejer_spectral_double_exp_le {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    Real.exp (Real.exp (112 * section13Q ((alpha / 2) ^ (4207554485 : Nat)))) ≤
      Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) := by
  let delta := (alpha / 2) ^ (4207554485 : Nat)
  have hδ : 0 < delta := by dsimp [delta]; positivity
  apply Real.exp_le_exp.mpr (Real.exp_le_exp.mpr _)
  have hs := section13_fejer_spectral_upper hα hαone
  have ht : 2 ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hQ0 : 0 ≤ section13Q delta := by
    unfold section13Q
    exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg hδ.le _)
  have h8 : (8 : Real) ≤ (2 / alpha) ^ (3 : Nat) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) ht 3
    norm_num at h ⊢
    exact h
  calc
    _ ≤ (8 * 15) * section13Q delta :=
      mul_le_mul_of_nonneg_right (by norm_num : (112 : Real) ≤ 8 * 15) hQ0
    _ = 8 * (15 * section13Q delta) := mul_assoc _ _ _
    _ ≤ 8 * (2 / alpha) ^ ((2 : Nat) ^ 53) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ (2 / alpha) ^ (3 : Nat) * (2 / alpha) ^ ((2 : Nat) ^ 53) :=
      mul_le_mul_of_nonneg_right h8 (by positivity)
    _ = (2 / alpha) ^ (3 + (2 : Nat) ^ 53) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [ht]) (by norm_num)

/-- The complete geometric construction has a double-exponential threshold
at the improved Fourier graph density. -/
theorem section13_fejer_geometric_threshold_le_double_exp {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section13GeometricThreshold ((alpha / 2) ^ (4207554485 : Nat)) ≤
      Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) := by
  have hδ : 0 < (alpha / 2) ^ (4207554485 : Nat) := pow_pos (by positivity) _
  have hδone : (alpha / 2) ^ (4207554485 : Nat) ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith only [hαone])
  exact (section13GeometricThreshold_le_double_exp hδ hδone).trans
    (section13_fejer_spectral_double_exp_le hα hαone)

end LeanProofs.GowersSzemeredi
