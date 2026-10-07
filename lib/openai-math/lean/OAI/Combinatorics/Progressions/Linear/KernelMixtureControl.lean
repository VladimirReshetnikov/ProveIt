import Mathlib

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def kernelAverage {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) (x : X) : ℝ := ∫ t, K x t * g t ∂μ

theorem kernelAverage_lipschitz {X T : Type*} [PseudoMetricSpace X] [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) (C D : ℝ≥0)
    (hK : ∀ x, Integrable (K x) μ) (hg : AEStronglyMeasurable g μ)
    (hgC : ∀ t, ‖g t‖ ≤ C)
    (hmove : ∀ x y, (∫ t, |K x t - K y t| ∂μ) ≤ D * dist x y) :
    LipschitzWith (C * D) (kernelAverage μ K g) := by
  have hint (x) : Integrable (fun t => K x t * g t) μ :=
    (hK x).mul_bdd hg (Filter.Eventually.of_forall hgC)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |(∫ t, K x t * g t ∂μ) - ∫ t, K y t * g t ∂μ| ≤ _
  rw [← integral_sub (hint x) (hint y)]
  have hd : Integrable (fun t => |K x t - K y t|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hK x).sub (hK y)).norm
  have hpoint (t) : ‖K x t * g t - K y t * g t‖ ≤ (C : ℝ) * |K x t - K y t| := by
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hgC t) (abs_nonneg (K x t - K y t))
  have h := norm_integral_le_of_norm_le (hd.const_mul (C : ℝ)) (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at h
  rw [Real.norm_eq_abs] at h
  apply h.trans
  have hbound := mul_le_mul_of_nonneg_left (hmove x y) C.coe_nonneg
  simpa only [NNReal.coe_mul, mul_assoc] using hbound

theorem kernelAverage_nonneg {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ)
    (hK : ∀ x t, 0 ≤ K x t) (hg : ∀ t, 0 ≤ g t) (x : X) :
    0 ≤ kernelAverage μ K g x := integral_nonneg (fun t => mul_nonneg (hK x t) (hg t))

theorem kernelAverage_cap {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) {C : ℝ}
    (hK : ∀ x, Integrable (K x) μ) (hK0 : ∀ x t, 0 ≤ K x t)
    (hmass : ∀ x, (∫ t, K x t ∂μ) = 1) (hg : AEStronglyMeasurable g μ)
    (hgC : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : X) :
    kernelAverage μ K g x ≤ C := by
  have hnorm (t) : ‖g t‖ ≤ C := by simpa only [Real.norm_of_nonneg (hgC t).1] using (hgC t).2
  have hint : Integrable (fun t => K x t * g t) μ := (hK x).mul_bdd hg (Filter.Eventually.of_forall hnorm)
  have h := integral_mono hint ((hK x).mul_const C)
    (fun t => mul_le_mul_of_nonneg_left (hgC t).2 (hK0 x t))
  simpa only [kernelAverage, integral_mul_const, hmass, one_mul] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem fixedKernelMixture_lipschitz {X T : Type*} [PseudoMetricSpace X] [MeasurableSpace T]
    (μ : Measure T) (K : T → ℝ) (g : X → T → ℝ) (L : ℝ≥0)
    (hK : Integrable K μ) (hK0 : ∀ t, 0 ≤ K t) (hKmass : (∫ t, K t ∂μ) = 1)
    (hint : ∀ x, Integrable (fun t => K t * g x t) μ)
    (hLip : ∀ t, LipschitzWith L (fun x => g x t)) :
    LipschitzWith L (fun x => ∫ t, K t * g x t ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← integral_sub (hint x) (hint y)]
  have hpoint (t) : ‖K t * g x t - K t * g y t‖ ≤ K t * ((L : ℝ) * dist x y) := by
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hK0 t)]
    apply mul_le_mul_of_nonneg_left _ (hK0 t)
    simpa only [Real.dist_eq, Real.norm_eq_abs] using (hLip t).dist_le_mul x y
  have h := norm_integral_le_of_norm_le (hK.mul_const ((L : ℝ) * dist x y))
    (Filter.Eventually.of_forall hpoint)
  simpa only [Real.norm_eq_abs, integral_mul_const, hKmass, one_mul] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem fixedKernelMixture_difference_le {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (g f h : T → ℝ) (hg : Integrable g μ) (hg0 : ∀ t, 0 ≤ g t)
    (hgmass : (∫ t, g t ∂μ) = 1)
    (hf : Integrable (fun t => g t * f t) μ) (hh : Integrable (fun t => g t * h t) μ)
    {E : ℝ} (he : ∀ t, g t ≠ 0 → |f t-h t| ≤ E) :
    |(∫ t, g t * f t ∂μ) - ∫ t, g t * h t ∂μ| ≤ E := by
  rw [← integral_sub hf hh]
  have hb (t) : ‖g t * f t-g t * h t‖ ≤ g t * E := by
    by_cases ht : g t = 0
    · simp only [ht, zero_mul, sub_self, norm_zero, le_refl]
    · rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hg0 t), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (he t ht) (hg0 t)
  have hi := norm_integral_le_of_norm_le (hg.mul_const E) (Filter.Eventually.of_forall hb)
  simpa only [Real.norm_eq_abs, integral_mul_const, hgmass, one_mul] using hi

theorem fixedKernelMixture_abs_le {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (g f : T → ℝ) (hg : Integrable g μ) (hg0 : ∀ t, 0 ≤ g t)
    (hgmass : (∫ t, g t ∂μ) = 1) {H : ℝ}
    (hb : ∀ t, g t ≠ 0 → |f t| ≤ H) : |∫ t, g t * f t ∂μ| ≤ H := by
  have hpoint (t) : ‖g t * f t‖ ≤ g t * H := by
    by_cases ht : g t = 0
    · simp only [ht, zero_mul, norm_zero, le_refl]
    · rw [norm_mul, Real.norm_of_nonneg (hg0 t), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb t ht) (hg0 t)
  have hi := norm_integral_le_of_norm_le (hg.mul_const H) (Filter.Eventually.of_forall hpoint)
  simpa only [Real.norm_eq_abs, integral_mul_const, hgmass, one_mul] using hi

theorem fixedKernelMixture_lipschitzOn {X T : Type*} [PseudoMetricSpace X] [MeasurableSpace T]
    (μ : Measure T) (g : T → ℝ) (F : X → T → ℝ) (S : Set X) (L : ℝ≥0)
    (hg : Integrable g μ) (hg0 : ∀ t, 0 ≤ g t) (hgmass : (∫ t, g t ∂μ) = 1)
    (hint : ∀ x ∈ S, Integrable (fun t => g t * F x t) μ)
    (hLip : ∀ t, g t ≠ 0 → LipschitzOnWith L (fun x => F x t) S) :
    LipschitzOnWith L (fun x => ∫ t, g t * F x t ∂μ) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  exact fixedKernelMixture_difference_le μ g (F x) (F y) hg hg0 hgmass (hint x hx) (hint y hy)
    (fun t ht => (hLip t ht).dist_le_mul x hx y hy)

end Erdos3

end

end OAI
