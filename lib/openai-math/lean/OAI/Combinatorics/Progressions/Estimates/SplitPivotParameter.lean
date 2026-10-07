import OAI.Combinatorics.Progressions.Linear.PivotKernelAllowances
import OAI.Combinatorics.Progressions.Probability.PivotDensitySupport

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem splitPivotDensity_norm_le_cap {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (R H S : ℝ≥0) (hf : Continuous f) (hg : Continuous g)
    (hfs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hfb : ∀ p, ‖f p‖ ≤ H) (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (v : I → ℝ) :
    ‖pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v‖ ≤ pivotKernelCap J A R H := by
  rw [Real.norm_eq_abs, splitPivotDensity_formula A B C hf hg hfs hgs v]
  exact fixedKernelMixture_abs_le volume g _ (compactBox_integrable g hg S hgs) hg0 hgmass
    (fun n _ => pivotOutputDensity_norm_le_cap A B f R H hfs hfb (v-C n))

theorem splitPivotDensity_parameter_lipschitzOn {X I J N : Type*} [PseudoMetricSpace X]
    [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : X → (N → ℝ) →L[ℝ] (I → ℝ)) (T : Set X) (L R K S : ℝ≥0)
    (hC : LipschitzOnWith L C T) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : LipschitzWith K f) (hg : Continuous g)
    (hfs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1) (v : I → ℝ) :
    LipschitzOnWith (pivotKernelLip J A R K * L * S)
      (fun x => pivotOutputDensity A (splitFreeColumns B (C x)) (splitFreeProfile f g) v) T := by
  have hρ := pivotOutputDensity_lipschitz A B R K hf hfs
  have he : (fun x => pivotOutputDensity A (splitFreeColumns B (C x)) (splitFreeProfile f g) v) =
      (fun x => ∫ n, g n * pivotOutputDensity A B f (v-C x n)) :=
    funext (fun x => splitPivotDensity_formula A B (C x) hf.continuous hg hfs hgs v)
  rw [he]
  apply fixedKernelMixture_lipschitzOn volume g _ T _ (compactBox_integrable g hg S hgs) hg0 hgmass
  · intro x _
    exact compactBox_integrable _ (hg.mul (hρ.continuous.comp (by fun_prop))) S
      (fun n hn => by rw [hgs n hn, zero_mul])
  · intro n hn
    have hnS : ‖n‖ ≤ S := le_of_not_gt (fun h => hn (hgs n h))
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hdiff : dist (C x n) (C y n) ≤ (L : ℝ)*dist x y*S := by
      rw [dist_eq_norm]
      have hop : ‖C x n-C y n‖ ≤ ‖C x-C y‖*‖n‖ := (C x-C y).le_opNorm n
      have hxy : ‖C x-C y‖ ≤ (L : ℝ)*dist x y := by
        simpa only [dist_eq_norm] using hC.dist_le_mul x hx y hy
      exact hop.trans (mul_le_mul hxy hnS (norm_nonneg _) (by positivity))
    apply (hρ.dist_le_mul (v-C x n) (v-C y n)).trans
    rw [dist_sub_left]
    apply (mul_le_mul_of_nonneg_left hdiff (pivotKernelLip J A R K).coe_nonneg).trans_eq
    simp only [NNReal.coe_mul]
    ring

end Erdos3

end

end OAI
