import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchDensityIncrement

namespace OAI

section

namespace Erdos3

theorem exists_patch_reset_budget (s : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d T : ℕ) (L σ : ℝ), 0 ≤ L → 0 < σ → σ ≤ 1 →
      C * ((d : ℝ) + 1) * (L + 1) ≤ σ * T →
      0 < T ∧ K * ((d : ℝ) + 1) ≤ T ∧
      (2 : ℝ) ^ (s + 1) * s < T ∧ 24 * (d : ℝ) * s < T ∧
      8 * L * d * s * (2 : ℝ) ^ s ≤ σ * T ∧
      (2 : ℝ) ^ (2 * s + 3) ≤ σ * T := by
  let C := 2 * (K + (2 : ℝ) ^ (s + 1) * s + 24 * s +
    8 * s * (2 : ℝ) ^ s + (2 : ℝ) ^ (2 * s + 3) + 1)
  have ha : 0 ≤ (2 : ℝ) ^ (s + 1) * s := by positivity
  have hb : 0 ≤ 24 * (s : ℝ) := by positivity
  have hc : 0 ≤ 8 * (s : ℝ) * (2 : ℝ) ^ s := by positivity
  have hd : 0 ≤ (2 : ℝ) ^ (2 * s + 3) := by positivity
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  have hCK : K ≤ C := by dsimp [C]; nlinarith
  have hClift : (2 : ℝ) ^ (s + 1) * s < C := by dsimp [C]; nlinarith
  have hCfreeze : 24 * (s : ℝ) < C := by dsimp [C]; nlinarith
  have hCroom : 8 * (s : ℝ) * (2 : ℝ) ^ s ≤ C := by dsimp [C]; nlinarith
  have hClength : (2 : ℝ) ^ (2 * s + 3) ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro d T L σ hL hσ hσ1 hbound
  let U := ((d : ℝ) + 1) * (L + 1)
  have hU : 1 ≤ U := by dsimp [U]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hdU : (d : ℝ) + 1 ≤ U := by dsimp [U]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hLdU : L * d ≤ U := by dsimp [U]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hbound' : C * U ≤ σ * T := by simpa only [U, mul_assoc] using hbound
  have hCT : C * U ≤ T := hbound'.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) T])
  have hCT' : C ≤ T := (le_mul_of_one_le_right (by linarith) hU).trans hCT
  have hT : 0 < T := by exact_mod_cast (show (0 : ℝ) < T by linarith)
  refine ⟨hT, ?_, hClift.trans_le hCT', ?_, ?_, ?_⟩
  · exact (mul_le_mul hCK hdU (by positivity) (by linarith)).trans hCT
  · calc
      _ ≤ (24 * (s : ℝ)) * U := by nlinarith [mul_le_mul_of_nonneg_left hdU (by positivity : (0 : ℝ) ≤ 24 * s)]
      _ < C * U := mul_lt_mul_of_pos_right hCfreeze (by linarith)
      _ ≤ T := hCT
  · calc
      _ = (8 * (s : ℝ) * (2 : ℝ) ^ s) * (L * d) := by ring
      _ ≤ C * U := mul_le_mul hCroom hLdU (by positivity) (by linarith)
      _ ≤ σ * T := hbound'
  · exact (hClength.trans (le_mul_of_one_le_right (by linarith) hU)).trans hbound'

end Erdos3

end

end OAI
