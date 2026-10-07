import OAI.Combinatorics.Progressions.Sampling.WeightedUniformGridDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem weightedModerateGridApproximation_norm_le_sum
    {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (rows : Finset (Finset I)) (offset : B → ℤ)
    (shift z : rows → ℤ) (F : Finset (rows → Fin M)) :
    ‖weightedModerateGridApproximation c s K M rows offset shift z F‖ ≤
      ((K : ℝ) / M) ^ rows.card *
        ∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k‖ := by
  unfold weightedModerateGridApproximation
  rw [norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ k ∈ F, ‖(∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k) *
        (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z))‖ := norm_sum_le _ _
    _ = ∑ k ∈ F, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k‖ := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [norm_mul, norm_star, rectangularGridCharacter_norm, mul_one]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
      (fun _ _ _ => norm_nonneg _)

theorem weightedModerateGridApproximation_norm_le_cap
    {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (K M : ℕ) [NeZero M] (rows : Finset (Finset I)) (offset : B → ℤ)
    (shift z : rows → ℤ) (F : Finset (rows → Fin M)) {Q : ℝ}
    (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1)
    (hQ : (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k‖) ≤ Q) :
    ‖weightedModerateGridApproximation c s K M rows offset shift z F‖ ≤ Q := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hQ
  exact (weightedModerateGridApproximation_norm_le_sum c s K M rows offset shift z F).trans
    ((mul_le_mul_of_nonneg_left hQ (by positivity)).trans (mul_le_of_le_one_left hQ0 hscale))

theorem pmf_complex_average_norm_le {X : Type*} (p : PMF X) (f : X → ℂ) {Q : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ Q) : ‖∑' x, ((p x).toReal : ℂ) * f x‖ ≤ Q := by
  have hw : HasSum (fun x => (p x).toReal * Q) Q := by
    simpa only [one_mul] using (pmf_toReal_hasSum p).mul_right Q
  apply tsum_of_norm_bounded hw
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf x) ENNReal.toReal_nonneg

end Erdos3

end

end OAI
