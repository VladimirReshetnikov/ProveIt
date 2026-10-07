import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {J : Type*} [Fintype J] (p : FiniteProbabilityWeights J)

theorem norm_complexMean_weighted_sub_le (c f g : J → ℂ) {B ε : ℝ}
    (hB : 0 ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hfg : ∀ j, ‖f j - g j‖ ≤ ε) :
    ‖p.complexMean (fun j => c j * f j) - p.complexMean (fun j => c j * g j)‖ ≤
      B * ε := by
  apply (p.norm_complexMean_sub_le _ _ (fun _ => B * ε) ?_).trans_eq
    (p.mean_const (B * ε))
  intro j _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (hc j) (hfg j) (norm_nonneg _) hB

theorem abs_re_complexMean_weighted_sub_le (c f g : J → ℂ) {B ε : ℝ}
    (hB : 0 ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hfg : ∀ j, ‖f j - g j‖ ≤ ε) :
    |(p.complexMean (fun j => c j * f j)).re -
      (p.complexMean (fun j => c j * g j)).re| ≤ B * ε := by
  exact (Complex.abs_re_le_norm
    (p.complexMean (fun j => c j * f j) - p.complexMean (fun j => c j * g j))).trans
      (p.norm_complexMean_weighted_sub_le c f g hB hc hfg)

theorem re_complexMean_weighted_lower_of_perturbation (c f g : J → ℂ) {B ε δ : ℝ}
    (hB : 0 ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hfg : ∀ j, ‖f j - g j‖ ≤ ε)
    (hscore : δ ≤ (p.complexMean (fun j => c j * g j)).re) :
    δ - B * ε ≤ (p.complexMean (fun j => c j * f j)).re := by
  have h := (abs_sub_le_iff.mp (p.abs_re_complexMean_weighted_sub_le c f g hB hc hfg)).2
  linarith

theorem norm_complexMean_weighted_lower_of_perturbation (c f g : J → ℂ) {B ε δ : ℝ}
    (hB : 0 ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hfg : ∀ j, ‖f j - g j‖ ≤ ε)
    (hscore : δ ≤ ‖p.complexMean (fun j => c j * g j)‖) :
    δ - B * ε ≤ ‖p.complexMean (fun j => c j * f j)‖ := by
  have he := p.norm_complexMean_weighted_sub_le c f g hB hc hfg
  have ht := norm_le_norm_sub_add (p.complexMean (fun j => c j * g j))
    (p.complexMean (fun j => c j * f j))
  rw [norm_sub_rev] at ht
  linarith

end Erdos3.FiniteProbabilityWeights

end

end OAI
