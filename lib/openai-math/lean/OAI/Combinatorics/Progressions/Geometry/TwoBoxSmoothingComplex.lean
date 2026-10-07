import OAI.Combinatorics.Progressions.Probability.DiagonalDensityTransport

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def twoBoxDifferenceDensity (ℓ r : ι → ℝ)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : (ι → ℝ) → ℝ :=
  affineBoxAverage ℓ A.toContinuousLinearMap (linearBoxDensity r B)

theorem twoBoxDifferenceDensity_mem_Icc (ℓ r : ι → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    twoBoxDifferenceDensity ℓ r A B x ∈ Set.Icc (0 : ℝ) (linearBoxDensityCap r hr B) :=
  affineBoxAverage_mem_Icc ℓ hℓ A _ (linearBoxDensity_measurable r B)
    (linearBoxDensity_mem_Icc r hr B) x

theorem twoBoxDifferenceDensity_lipschitz [DecidableEq ι] (ℓ r : ι → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    LipschitzWith ((linearBoxDensityCap r hr B * boxWindowTranslationBound ℓ hℓ) *
      ‖A.symm.toContinuousLinearMap‖₊) (twoBoxDifferenceDensity ℓ r A B) := by
  apply affineBoxAverage_lipschitz ℓ hℓ A _ _ (linearBoxDensity_measurable r B)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (linearBoxDensity_mem_Icc r hr B x).1]
  exact (linearBoxDensity_mem_Icc r hr B x).2

theorem twoBoxDifferenceDensity_integrable (ℓ r : ι → ℝ)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : Integrable (twoBoxDifferenceDensity ℓ r A B) :=
  affineBoxAverage_integrable ℓ A.toContinuousLinearMap _
    (linearBoxDensity_measurable r B) (linearBoxDensity_integrable r B)

theorem twoBoxDifferenceDensity_mass (ℓ r : ι → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : (∫ x, twoBoxDifferenceDensity ℓ r A B x) = 1 := by
  unfold twoBoxDifferenceDensity
  rw [affineBoxAverage_mass ℓ hℓ _ _ (linearBoxDensity_measurable r B)
    (linearBoxDensity_integrable r B), linearBoxDensity_mass r hr]

theorem twoBoxDifferenceDensity_test_integral (ℓ r : ι → ℝ)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (φ : (ι → ℝ) → ℝ)
    (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, twoBoxDifferenceDensity ℓ r A B x * φ x) =
      ∫ u, boxProbabilityWindow ℓ 0 u *
        ∫ v, boxProbabilityWindow r 0 v * φ (B v - A u) := by
  unfold twoBoxDifferenceDensity
  rw [affineBoxAverage_test_integral ℓ _ _ φ
    (linearBoxDensity_measurable r B) (linearBoxDensity_integrable r B) hφ hφC]
  apply integral_congr_ae
  filter_upwards [] with u
  congr 1
  exact linearDensityPullback_test_integral B _ (fun y => φ (y - A u))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem affineBoxAverage_preserves_lipschitz (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ) (L : ℝ≥0)
    (hg : LipschitzWith L g) {C : ℝ} (hbound : ∀ x, ‖g x‖ ≤ C) :
    LipschitzWith L (affineBoxAverage ℓ A g) := by
  apply fixedKernelMixture_lipschitz volume (boxProbabilityWindow ℓ 0)
    (fun x u => g (x + A u)) L (boxProbabilityWindow_integrable ℓ 0)
    (boxProbabilityWindow_nonneg ℓ hℓ 0) (boxProbabilityWindow_mass ℓ hℓ 0)
  · intro x
    exact (boxProbabilityWindow_integrable ℓ 0).mul_bdd
      (hg.continuous.comp (continuous_const.add A.continuous)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => hbound (x + A u)))
  · intro u
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using hg.dist_le_mul (x + A u) (y + A u)

theorem affineBoxAverage_preserves_cap (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ)
    (hg : Measurable g) {C : ℝ} (hbound : ∀ x, g x ∈ Set.Icc (0 : ℝ) C)
    (x : ι → ℝ) : affineBoxAverage ℓ A g x ∈ Set.Icc (0 : ℝ) C := by
  have hnorm (u) : ‖g (x + A u)‖ ≤ C := by
    rw [Real.norm_of_nonneg (hbound _).1]
    exact (hbound _).2
  have hint : Integrable (fun u => boxProbabilityWindow ℓ 0 u * g (x + A u)) :=
    (boxProbabilityWindow_integrable ℓ 0).mul_bdd
      (hg.comp (measurable_const.add A.continuous.measurable)).aestronglyMeasurable
      (Filter.Eventually.of_forall hnorm)
  refine ⟨affineBoxAverage_nonneg ℓ hℓ A g (fun y => (hbound y).1) x, ?_⟩
  have h := integral_mono hint ((boxProbabilityWindow_integrable ℓ 0).mul_const C)
    (fun u => mul_le_mul_of_nonneg_left (hbound _).2 (boxProbabilityWindow_nonneg ℓ hℓ 0 u))
  simpa only [affineBoxAverage, integral_mul_const, boxProbabilityWindow_mass ℓ hℓ 0, one_mul] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem integral_comp_inverse_linear_complex
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (f : (ι → ℝ) → ℂ) :
    (∫ x, f (A.symm x)) = (((inverseJacobian A)⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
  have h := A.symm.toHomeomorph.measurableEmbedding.integral_map (μ := volume) f
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [inverse_map_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (inverseJacobian_pos A).le)] at h
  simpa only [Complex.real_smul] using h.symm

theorem linearDensityPullback_complex_test_integral
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (f : (ι → ℝ) → ℝ) (φ : (ι → ℝ) → ℂ) :
    (∫ x, (linearDensityPullback A f x : ℂ) * φ x) =
      ∫ u, (f u : ℂ) * φ (A u) := by
  have he (x : ι → ℝ) : (linearDensityPullback A f x : ℂ) * φ x =
      (inverseJacobian A : ℂ) *
        ((f (A.symm x) : ℂ) * φ (A (A.symm x))) := by
    simp only [linearDensityPullback, Complex.ofReal_mul, A.apply_symm_apply, mul_assoc]
  simp_rw [he]
  rw [integral_const_mul,
    integral_comp_inverse_linear_complex A (fun u => (f u : ℂ) * φ (A u)),
    ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (inverseJacobian_pos A).ne',
    Complex.ofReal_one, one_mul]

theorem affineBoxAverage_complex_test_integral (ℓ : ι → ℝ)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ) (φ : (ι → ℝ) → ℂ)
    (hg : Measurable g) (hgi : Integrable g) (hφ : Measurable φ)
    {C : ℝ} (hφC : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, (affineBoxAverage ℓ A g x : ℂ) * φ x) =
      ∫ u, (boxProbabilityWindow ℓ 0 u : ℂ) * ∫ y, (g y : ℂ) * φ (y - A u) := by
  have hi : Integrable (Function.uncurry
      (fun x u => ((boxProbabilityWindow ℓ 0 u * g (x + A u) : ℝ) : ℂ) * φ x))
      (volume.prod volume) :=
    (affineBoxIntegrand_integrable ℓ A g hg hgi).ofReal.mul_bdd
      (hφ.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hφC p.1))
  calc
    (∫ x, (affineBoxAverage ℓ A g x : ℂ) * φ x) =
        ∫ x, ∫ u, ((boxProbabilityWindow ℓ 0 u * g (x + A u) : ℝ) : ℂ) * φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_mul_const,
        integral_complex_ofReal (f := fun a => boxProbabilityWindow ℓ 0 a * g (x + A a))]
      rfl
    _ = ∫ u, ∫ x, ((boxProbabilityWindow ℓ 0 u * g (x + A u) : ℝ) : ℂ) * φ x :=
      integral_integral_swap hi
    _ = ∫ u, (boxProbabilityWindow ℓ 0 u : ℂ) * ∫ y, (g y : ℂ) * φ (y - A u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [Complex.ofReal_mul, mul_assoc, integral_const_mul]
      congr 1
      have h := integral_add_right_eq_self (μ := volume)
        (fun y => (g y : ℂ) * φ (y - A u)) (A u)
      simpa only [add_sub_cancel_right] using h

theorem twoBoxDifferenceDensity_complex_test_integrable (ℓ r : ι → ℝ)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (φ : (ι → ℝ) → ℂ)
    (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, ‖φ x‖ ≤ C) :
    Integrable (fun x => (twoBoxDifferenceDensity ℓ r A B x : ℂ) * φ x) :=
  (twoBoxDifferenceDensity_integrable ℓ r A B).ofReal.mul_bdd
    hφ.aestronglyMeasurable (Filter.Eventually.of_forall hφC)

theorem twoBoxDifferenceDensity_complex_test_integral (ℓ r : ι → ℝ)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (φ : (ι → ℝ) → ℂ)
    (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, (twoBoxDifferenceDensity ℓ r A B x : ℂ) * φ x) =
      ∫ u, (boxProbabilityWindow ℓ 0 u : ℂ) *
        ∫ v, (boxProbabilityWindow r 0 v : ℂ) * φ (B v - A u) := by
  unfold twoBoxDifferenceDensity
  rw [affineBoxAverage_complex_test_integral ℓ _ _ φ
    (linearBoxDensity_measurable r B) (linearBoxDensity_integrable r B) hφ hφC]
  apply integral_congr_ae
  filter_upwards [] with u
  congr 1
  exact linearDensityPullback_complex_test_integral B _ (fun y => φ (y - A u))

end Erdos3

end

end OAI
