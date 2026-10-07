import OAI.Combinatorics.Progressions.Polynomial.JointExceptionalPolynomialBudget

namespace OAI

section

namespace Erdos3

noncomputable def jointSpatialError (gainLog : ℝ) : ℝ :=
  Real.exp (-gainLog) / 128

private theorem jointExceptional_exp_eight : (256 : ℝ) ≤ Real.exp 8 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 8
  norm_num [← Real.exp_nat_mul] at hp ⊢
  exact hp

theorem jointSpatialError_pos (gainLog : ℝ) : 0 < jointSpatialError gainLog := by
  unfold jointSpatialError
  positivity

theorem jointSpatialError_inverse_le_exp (gainLog : ℝ) :
    (jointSpatialError gainLog)⁻¹ ≤ Real.exp (gainLog + 8) := by
  have he : 0 < Real.exp gainLog := Real.exp_pos _
  calc
    (jointSpatialError gainLog)⁻¹ = 128 * Real.exp gainLog := by
      simp [jointSpatialError, Real.exp_neg]
    _ ≤ Real.exp 8 * Real.exp gainLog := by
      exact mul_le_mul_of_nonneg_right (by linarith [jointExceptional_exp_eight]) he.le
    _ = Real.exp (gainLog + 8) := by rw [← Real.exp_add]; congr 1; ring

theorem jointExceptionalGainBudget {gainLog gain P : ℝ}
    (hg : 0 ≤ gainLog) (hP : gainLog + 8 ≤ P)
    (hgain : Real.exp (-gainLog) ≤ gain) :
    Real.exp (-(gainLog + 8)) + jointSpatialError gainLog / 2 +
      6 * positiveProjectionAccuracy P ≤ (gain / 4) / 4 := by
  have he : 0 < Real.exp (-gainLog) := Real.exp_pos _
  have hshift : Real.exp (-(gainLog + 8)) ≤ Real.exp (-gainLog) / 256 := by
    rw [neg_add, Real.exp_add, Real.exp_neg (8 : ℝ), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left he.le (by norm_num) jointExceptional_exp_eight
  have hprecision : positiveProjectionAccuracy P ≤ Real.exp (-gainLog) / 256 := by
    apply le_trans _ hshift
    apply Real.exp_le_exp.mpr
    change -(2 * P + 4) ≤ -(gainLog + 8)
    linarith
  unfold jointSpatialError
  linarith

theorem exists_jointSpatialError_polynomial_budget :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P₀ gainLog : ℝ} {n : ℕ}, 0 ≤ P₀ →
      0 < n → (n : ℝ) ≤ P₀ → 0 ≤ gainLog → gainLog ≤ P₀ →
      (spatialMatrixBlockThreshold n (jointSpatialError gainLog))⁻¹ ≤
          Real.exp ((P₀ + A)^A) ∧
      (2 / spatialMatrixBlockThreshold n (jointSpatialError gainLog)) *
          ((n * n.factorial : ℕ) : ℝ) ≤ Real.exp ((P₀ + A)^A) ∧
      smoothMatrixBlockWidthLogBudget (2*n*n) n 2 (gainLog+8) ≤ (P₀+A)^A := by
  obtain ⟨A, hA, hbudget⟩ := exists_jointExceptional_polynomial_budget
  refine ⟨A, hA, ?_⟩
  intro P₀ gainLog n hP hn hnP hg hgP
  obtain ⟨hthreshold, hwidth⟩ := hbudget hP hnP hg hgP
  have hη := jointSpatialError_pos gainLog
  have hηb := jointSpatialError_inverse_le_exp gainLog
  have hE : 0 ≤ gainLog + 8 := by linarith
  have hthreshold' : smoothMatrixBlockThresholdLogBudget (2*n*n) n 2
      (gainLog+8) ≤ (P₀+A)^A := by nlinarith [sq_nonneg ((n : ℝ)+1)]
  exact ⟨(spatialMatrixBlockThreshold_inverse_le_exp hn hη hE hηb).trans
      (Real.exp_le_exp.mpr hthreshold'),
    (spatialMatrixBlockCutoff_lip_exp_budget hn hη hE hηb).trans
      (Real.exp_le_exp.mpr hthreshold), hwidth⟩

end Erdos3

end

end OAI
