import OAI.Combinatorics.Progressions.Geometry.BoxWindowAveraging

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem normalizedIntervalWindow_translate (ℓ x t : ℝ) :
    normalizedIntervalWindow ℓ x t = normalizedIntervalWindow ℓ 0 (t - x) := by
  have hm : t ∈ Set.Ioc x (x + ℓ) ↔ t - x ∈ Set.Ioc 0 (0 + ℓ) := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [normalizedIntervalWindow, intervalWindow, Set.indicator, hm]

variable {ι : Type*} [Fintype ι]

theorem boxProbabilityWindow_translate (ℓ x t : ι → ℝ) :
    boxProbabilityWindow ℓ x t = boxProbabilityWindow ℓ 0 (t - x) := by
  apply Finset.prod_congr rfl
  intro i _
  exact normalizedIntervalWindow_translate _ _ _

theorem boxAverage_eq_translate (ℓ : ι → ℝ) (g : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    kernelAverage volume (boxProbabilityWindow ℓ) g x =
      ∫ u, boxProbabilityWindow ℓ 0 u * g (u + x) := by
  change (∫ t, boxProbabilityWindow ℓ x t * g t) = _
  rw [← integral_add_right_eq_self (fun t => boxProbabilityWindow ℓ x t * g t) x]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [boxProbabilityWindow_translate, add_sub_cancel_right]

noncomputable def affineBoxAverage (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ u, boxProbabilityWindow ℓ 0 u * g (x + A u)

theorem affineBoxAverage_eq (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    affineBoxAverage ℓ A.toContinuousLinearMap g x =
      kernelAverage volume (boxProbabilityWindow ℓ) (fun t => g (A t)) (A.symm x) := by
  rw [boxAverage_eq_translate]
  unfold affineBoxAverage
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [map_add, A.apply_symm_apply, ContinuousLinearEquiv.coe_coe, add_comm]

theorem affineBoxAverage_lipschitz [DecidableEq ι] (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ) (C : ℝ≥0)
    (hg : Measurable g) (hbound : ∀ t, ‖g t‖ ≤ C) :
    LipschitzWith ((C * boxWindowTranslationBound ℓ hℓ) * ‖A.symm.toContinuousLinearMap‖₊)
      (affineBoxAverage ℓ A.toContinuousLinearMap g) := by
  have h := (boxAverage_lipschitz ℓ hℓ (fun t => g (A t)) C
    (hg.comp A.continuous.measurable).aestronglyMeasurable (fun t => hbound (A t))).comp
      A.symm.toContinuousLinearMap.lipschitzWith
  have heq : (fun x => kernelAverage volume (boxProbabilityWindow ℓ)
      (fun t => g (A t)) (A.symm.toContinuousLinearMap x)) =
      affineBoxAverage ℓ A.toContinuousLinearMap g := by
    funext x
    exact (affineBoxAverage_eq ℓ A g x).symm
  change LipschitzWith _ (fun x => kernelAverage volume (boxProbabilityWindow ℓ)
    (fun t => g (A t)) (A.symm.toContinuousLinearMap x)) at h
  rw [heq] at h
  exact h

theorem affineBoxAverage_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ) {C : ℝ}
    (hg : Measurable g) (hbound : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : ι → ℝ) :
    affineBoxAverage ℓ A.toContinuousLinearMap g x ∈ Set.Icc (0 : ℝ) C := by
  rw [affineBoxAverage_eq]
  exact boxAverage_mem_Icc ℓ hℓ _ (hg.comp A.continuous.measurable).aestronglyMeasurable
    (fun t => hbound (A t)) _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def affineBoxIntegrand (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  boxProbabilityWindow ℓ 0 p.2 * g (p.1 + A p.2)

theorem affineBoxIntegrand_integrable (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (hg : Measurable g) (hgi : Integrable g) :
    Integrable (affineBoxIntegrand ℓ A g) (volume.prod volume) := by
  have hm : Measurable (affineBoxIntegrand ℓ A g) :=
    ((boxProbabilityWindow_measurable ℓ 0).comp measurable_snd).mul
      (hg.comp (measurable_fst.add (A.continuous.measurable.comp measurable_snd)))
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with u
    exact (hgi.comp_add_right (A u)).const_mul (boxProbabilityWindow ℓ 0 u)
  · have heq (u : ι → ℝ) : (∫ x, ‖affineBoxIntegrand ℓ A g (x, u)‖) =
        ‖boxProbabilityWindow ℓ 0 u‖ * ∫ x, ‖g x‖ := by
      simp only [affineBoxIntegrand, norm_mul]
      rw [integral_const_mul, integral_add_right_eq_self (fun x => ‖g x‖) (A u)]
    simp_rw [heq]
    exact (boxProbabilityWindow_integrable ℓ 0).norm.mul_const _

theorem affineBoxAverage_integrable (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (hg : Measurable g) (hgi : Integrable g) :
    Integrable (affineBoxAverage ℓ A g) :=
  (affineBoxIntegrand_integrable ℓ A g hg hgi).integral_prod_left

theorem affineBoxAverage_mass (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ)
    (hg : Measurable g) (hgi : Integrable g) :
    (∫ x, affineBoxAverage ℓ A g x) = ∫ x, g x := by
  have hi : Integrable (Function.uncurry
      (fun x u => boxProbabilityWindow ℓ 0 u * g (x + A u))) (volume.prod volume) :=
    affineBoxIntegrand_integrable ℓ A g hg hgi
  change (∫ x, ∫ u, boxProbabilityWindow ℓ 0 u * g (x + A u)) = _
  rw [integral_integral_swap hi]
  simp_rw [integral_const_mul, integral_add_right_eq_self]
  rw [integral_mul_const, boxProbabilityWindow_mass ℓ hℓ 0, one_mul]

theorem affineBoxAverage_nonneg (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ)
    (hg : ∀ x, 0 ≤ g x) (x : ι → ℝ) : 0 ≤ affineBoxAverage ℓ A g x :=
  integral_nonneg (fun u => mul_nonneg (boxProbabilityWindow_nonneg ℓ hℓ 0 u) (hg _))

theorem affineBoxAverage_probability_density (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ)
    (hg : Measurable g) (hgi : Integrable g) (hg0 : ∀ x, 0 ≤ g x) (hgmass : (∫ x, g x) = 1) :
    (∀ x, 0 ≤ affineBoxAverage ℓ A g x) ∧ Integrable (affineBoxAverage ℓ A g) ∧
      (∫ x, affineBoxAverage ℓ A g x) = 1 :=
  ⟨affineBoxAverage_nonneg ℓ hℓ A g hg0,
    affineBoxAverage_integrable ℓ A g hg hgi, (affineBoxAverage_mass ℓ hℓ A g hg hgi).trans hgmass⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

theorem affineBoxAverage_test_integral (ℓ : ι → ℝ)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (g φ : (ι → ℝ) → ℝ)
    (hg : Measurable g) (hgi : Integrable g) (hφ : Measurable φ)
    {C : ℝ} (hφC : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, affineBoxAverage ℓ A g x * φ x) =
      ∫ u, boxProbabilityWindow ℓ 0 u * ∫ y, g y * φ (y - A u) := by
  have hi : Integrable (Function.uncurry
      (fun x u => (boxProbabilityWindow ℓ 0 u * g (x + A u)) * φ x))
      (volume.prod volume) :=
    (affineBoxIntegrand_integrable ℓ A g hg hgi).mul_bdd
      (hφ.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hφC p.1))
  calc
    (∫ x, affineBoxAverage ℓ A g x * φ x) =
        ∫ x, ∫ u, (boxProbabilityWindow ℓ 0 u * g (x + A u)) * φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ u, ∫ x, (boxProbabilityWindow ℓ 0 u * g (x + A u)) * φ x :=
      integral_integral_swap hi
    _ = ∫ u, boxProbabilityWindow ℓ 0 u * ∫ y, g y * φ (y - A u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [mul_assoc, integral_const_mul]
      congr 1
      have h := integral_add_right_eq_self (μ := volume) (fun y => g y * φ (y - A u)) (A u)
      simpa only [add_sub_cancel_right] using h

end Erdos3

end

end OAI
