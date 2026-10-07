import OAI.Combinatorics.Progressions.Polynomial.LocalizationPolynomialScales

namespace OAI

section

namespace Erdos3

noncomputable def localizationThreshold (U ζ : ℝ) (i : ℕ) : ℝ := ζ / (2 * U ^ 2) ^ i

theorem localizationThreshold_pos {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ) (i : ℕ) :
    0 < localizationThreshold U ζ i := by unfold localizationThreshold; positivity

theorem localizationThreshold_zero (U ζ : ℝ) : localizationThreshold U ζ 0 = ζ := by
  simp only [localizationThreshold, pow_zero, div_one]

theorem localizationThreshold_antitone {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 ≤ ζ)
    {i j : ℕ} (hij : i ≤ j) : localizationThreshold U ζ j ≤ localizationThreshold U ζ i := by
  have hC : 1 ≤ 2 * U ^ 2 := by nlinarith [one_le_pow₀ hU (n := 2)]
  apply div_le_div_of_nonneg_left hζ (by positivity)
  exact pow_le_pow_right₀ hC hij

theorem localizationThreshold_le_one {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (i : ℕ) :
    localizationThreshold U ζ i ≤ 1 := by
  have h := localizationThreshold_antitone hU hζ.le (Nat.zero_le i)
  rw [localizationThreshold_zero] at h
  exact h.trans hζ1

theorem localizationThreshold_step {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ)
    {i m : ℕ} (hi : i + 1 ≤ m) :
    localizationThreshold U ζ m + U ^ 2 * localizationThreshold U ζ (i + 1) ≤
      localizationThreshold U ζ i := by
  have hε := localizationThreshold_antitone hU hζ.le hi
  have hη := localizationThreshold_pos hU hζ (i + 1)
  have hp : 1 ≤ U ^ 2 := one_le_pow₀ hU
  have he : localizationThreshold U ζ i =
      2 * U ^ 2 * localizationThreshold U ζ (i + 1) := by
    have hC : 2 * U ^ 2 ≠ 0 := by positivity
    unfold localizationThreshold
    rw [pow_succ]
    field_simp
    exact pow_succ' _ _
  rw [he]
  nlinarith

end Erdos3

end

end OAI
