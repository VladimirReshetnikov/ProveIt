import OAI.Combinatorics.Progressions.Estimates.ModeRemovalThresholds

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def modeAmplitudeAccuracy (L ε : ℝ) : ℝ := ε / (2 * (L + 1))

theorem modeAmplitudeAccuracy_pos {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    0 < modeAmplitudeAccuracy L ε := by
  unfold modeAmplitudeAccuracy
  positivity

theorem modeRemovalRadius_le_error (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    modeRemovalRadius d ε ≤ ε := by
  have hc := modeRemovalTranslationConstant_nonneg d
  unfold modeRemovalRadius
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem modeAmplitudeError_bound (d : ℕ) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    modeRemovalTranslationConstant d * modeRemovalRadius d (modeAmplitudeAccuracy L ε) +
      L * modeRemovalRadius d (modeAmplitudeAccuracy L ε) +
      modeRemovalBeta (modeAmplitudeAccuracy L ε) ≤ ε := by
  have he := modeAmplitudeAccuracy_pos hL hε
  have hbase := modeRemovalError_bound d he
  have hr := modeRemovalRadius_le_error d he
  have hmul := mul_le_mul_of_nonneg_left hr hL
  have hidentity : (L + 1) * modeAmplitudeAccuracy L ε = ε / 2 := by
    unfold modeAmplitudeAccuracy
    field_simp
  nlinarith

theorem modeAmplitudeAccuracy_inv_le_exp {P L ε : ℝ}
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hLP : L ≤ Real.exp P)
    (hε : 0 < ε) (hεP : 1 / ε ≤ Real.exp P) :
    1 / modeAmplitudeAccuracy L ε ≤ Real.exp (2 * P + 2) := by
  have hden : 0 < L + 1 := by linarith
  have hone : 1 ≤ Real.exp P := Real.one_le_exp hP
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = 2 * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 := mul_le_mul htwo htwo (by norm_num) (Real.exp_nonneg 1)
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hinv : 1 / modeAmplitudeAccuracy L ε = 2 * (L + 1) * (1 / ε) := by
    unfold modeAmplitudeAccuracy
    field_simp
  rw [hinv]
  calc
    _ ≤ 4 * Real.exp P * Real.exp P := by
      have hfactor : 2 * (L + 1) ≤ 4 * Real.exp P := by linarith
      exact mul_le_mul hfactor hεP (by positivity) (by positivity)
    _ ≤ Real.exp 2 * Real.exp P * Real.exp P := by gcongr
    _ = Real.exp (2 * P + 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3.VectorPolynomial

end

end OAI
