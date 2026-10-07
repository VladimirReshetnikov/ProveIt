import OAI.Combinatorics.Progressions.Geometry.PivotCoordinateChange
import OAI.Combinatorics.Progressions.Probability.PairedProductDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def pivotOutputDensity (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (v : I → ℝ) : ℝ := ∫ y, pivotDensityPullback A B f (y, v)

omit [Fintype I] in
theorem pivotOutputDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, f (y, A.symm (v - B y)) := by
  exact integral_const_mul _ _

theorem pivotOutputDensity_measurable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Measurable f) : Measurable (pivotOutputDensity A B f) :=
  (pivotDensityPullback_measurable A B hf).stronglyMeasurable.integral_prod_left'.measurable

omit [Fintype I] in
theorem pivotOutputDensity_nonneg (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : ∀ p, 0 ≤ f p) (v : I → ℝ) : 0 ≤ pivotOutputDensity A B f v :=
  integral_nonneg fun _ => mul_nonneg (inverseJacobian_pos A).le (hf _)

theorem pivotOutputDensity_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (pivotOutputDensity A B f) :=
  (pivotDensityPullback_integrable A B hf).integral_prod_right

theorem pivotOutputDensity_integral (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) : (∫ v, pivotOutputDensity A B f v) = ∫ p, f p := by
  unfold pivotOutputDensity
  rw [← integral_prod_symm _ (pivotDensityPullback_integrable A B hf)]
  exact pivotDensityPullback_integral A B f

theorem pivotOutputDensity_test_integral (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) (φ : (I → ℝ) → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hC : ∀ v, ‖φ v‖ ≤ C) :
    (∫ v, pivotOutputDensity A B f v * φ v) =
      ∫ p, f p * φ (A p.2 + B p.1) := by
  have hi : Integrable (fun p : (J → ℝ) × (I → ℝ) => pivotDensityPullback A B f p * φ p.2) :=
    (pivotDensityPullback_integrable A B hf).mul_bdd
      (hφ.comp measurable_snd).aestronglyMeasurable (Filter.Eventually.of_forall fun p => hC p.2)
  calc
    _ = ∫ v, ∫ y, pivotDensityPullback A B f (y, v) * φ v := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact (integral_mul_const _ _).symm
    _ = ∫ p : (J → ℝ) × (I → ℝ), pivotDensityPullback A B f p * φ p.2 :=
      (integral_prod_symm _ hi).symm
    _ = _ := pivotDensityPullback_test_integral A B f (fun p => φ p.2)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotOutputDensity_l1_contract
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f g : (J → ℝ) × (I → ℝ) → ℝ) (hf : Integrable f) (hg : Integrable g) :
    (∫ v, |pivotOutputDensity A B f v - pivotOutputDensity A B g v|) ≤ ∫ p, |f p - g p| := by
  have hF := pivotDensityPullback_integrable A B hf
  have hG := pivotDensityPullback_integrable A B hg
  have he := densityMixture_l1_le (volume : Measure (J → ℝ)) (volume : Measure (I → ℝ))
    (fun y v => pivotDensityPullback A B f (y, v))
    (fun y v => pivotDensityPullback A B g (y, v)) hF hG
  change (∫ v, ‖pivotOutputDensity A B f v - pivotOutputDensity A B g v‖) ≤ _ at he
  have hdiff : Integrable (fun p => ‖pivotDensityPullback A B f p - pivotDensityPullback A B g p‖) :=
    (hF.sub hG).norm
  rw [← integral_prod _ hdiff] at he
  have hnorm : (fun p => ‖pivotDensityPullback A B f p - pivotDensityPullback A B g p‖) =
      pivotDensityPullback A B (fun p => |f p - g p|) := by
    funext p
    simp only [pivotDensityPullback, ← mul_sub, Real.norm_eq_abs, abs_mul,
      abs_of_pos (inverseJacobian_pos A)]
  rw [hnorm] at he
  change (∫ v, ‖pivotOutputDensity A B f v - pivotOutputDensity A B g v‖) ≤
    ∫ p, pivotDensityPullback A B (fun p => |f p - g p|) p at he
  rw [pivotDensityPullback_integral] at he
  simpa only [Real.norm_eq_abs] using he

omit [Fintype I] in
theorem pivotOutputDensity_translate
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f : (J → ℝ) × (I → ℝ) → ℝ) (v z : I → ℝ) :
    pivotOutputDensity A B f (v + z) =
      pivotOutputDensity A B (fun p => f (p + (0, A.symm z))) v := by
  rw [pivotOutputDensity_formula, pivotOutputDensity_formula]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  have harg : v + z - B y = (v - B y) + z := by abel
  change f (y, A.symm (v + z - B y)) = f (y + 0, A.symm (v - B y) + A.symm z)
  rw [harg, map_add, add_zero]

theorem pivotOutputDensity_translation_l1
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf : Integrable f) (a b : I → ℝ) :
    (∫ v, |pivotOutputDensity A B f (v + a) - pivotOutputDensity A B f (v + b)|) ≤
      ∫ p, |f (p + (0, A.symm a)) - f (p + (0, A.symm b))| := by
  simp_rw [pivotOutputDensity_translate]
  let : (volume : Measure ((J → ℝ) × (I → ℝ))).IsAddRightInvariant := by
    change (Measure.prod (volume : Measure (J → ℝ)) (volume : Measure (I → ℝ))).IsAddRightInvariant
    infer_instance
  exact pivotOutputDensity_l1_contract A B _ _ (hf.comp_add_right _) (hf.comp_add_right _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem pivotOutputDensity_law {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} (hf : Integrable f) (hf0 : ∀ p, 0 ≤ f p) :
    Measure.map (fun p => A p.2 + B p.1) (realDensityMeasure volume f) =
      realDensityMeasure volume (pivotOutputDensity A B f) := by
  have hm : Measurable (fun p : (J → ℝ) × (I → ℝ) => A p.2 + B p.1) := by fun_prop
  ext s hs
  rw [Measure.map_apply hm hs, realDensityMeasure_apply volume f hf hf0 (hm hs),
    realDensityMeasure_apply volume _ (pivotOutputDensity_integrable A B hf)
      (pivotOutputDensity_nonneg A B hf0) hs]
  congr 1
  have h := pivotOutputDensity_test_integral A B hf (s.indicator (fun _ => 1))
    (measurable_const.indicator hs) (C := 1) (fun x => by
      by_cases hx : x ∈ s <;> simp [hx])
  have hl (v : I → ℝ) :
      pivotOutputDensity A B f v * s.indicator (fun _ => 1) v =
        s.indicator (pivotOutputDensity A B f) v := by
    by_cases hv : v ∈ s <;> simp [hv]
  have hr (p : (J → ℝ) × (I → ℝ)) :
      f p * s.indicator (fun _ => 1) (A p.2 + B p.1) =
        ((fun p : (J → ℝ) × (I → ℝ) => A p.2 + B p.1) ⁻¹' s).indicator f p := by
    by_cases hp : A p.2 + B p.1 ∈ s <;> simp [hp]
  simp_rw [hl, hr] at h
  rw [integral_indicator hs, integral_indicator (hm hs)] at h
  exact h.symm

theorem pivotOutputDensity_probability {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} (hf : Integrable f) (hf0 : ∀ p, 0 ≤ f p)
    (hmass : (∫ p, f p) = 1) :
    IsProbabilityMeasure (realDensityMeasure volume (pivotOutputDensity A B f)) :=
  realDensityMeasure_probability volume _ (pivotOutputDensity_integrable A B hf)
    (pivotOutputDensity_nonneg A B hf0) ((pivotOutputDensity_integral A B hf).trans hmass)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem pivotOutputDensity_input_translate {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f : (J → ℝ) × (I → ℝ) → ℝ) (a : (J → ℝ) × (I → ℝ)) (v : I → ℝ) :
    pivotOutputDensity A B (fun p => f (p - a)) v =
      pivotOutputDensity A B f (v - (A a.2 + B a.1)) := by
  rw [pivotOutputDensity_formula, pivotOutputDensity_formula]
  congr 1
  let g := fun y => f (y, A.symm (v - (A a.2 + B a.1) - B y))
  calc
    _ = ∫ y, g (y - a.1) := by
      apply integral_congr_ae
      filter_upwards [] with y
      have harg : v - (A a.2 + B a.1) - B (y - a.1) = (v - B y) - A a.2 := by
        rw [map_sub]
        abel
      dsimp only [g]
      rw [harg, map_sub A.symm (v - B y) (A a.2), A.symm_apply_apply]
      rfl
    _ = ∫ y, g y := integral_sub_right_eq_self g a.1

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem translatedMixture_l1 {T I : Type*} [MeasurableSpace T] [Fintype I]
    (μ : Measure T) [IsProbabilityMeasure μ] (ρ : (I → ℝ) → ℝ)
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρ1 : (∫ x, ρ x) = 1) {D δ : ℝ} (hD : 0 ≤ D)
    (hρ : ∀ a b, (∫ x, |ρ (x + a) - ρ (x + b)|) ≤ D * dist a b)
    (F G : T → I → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hmove : ∀ᵐ t ∂μ, dist (F t) (G t) ≤ δ) :
    (∫ x, |(∫ t, ρ (x + F t) ∂μ) - ∫ t, ρ (x + G t) ∂μ|) ≤ D * δ := by
  have hi (H : T → I → ℝ) (hH : Measurable H) :
      Integrable (Function.uncurry (fun t x => ρ (x + H t)))
        (μ.prod (volume : Measure (I → ℝ))) := by
    apply densityMixture_joint_integrable μ volume (fun t x => ρ (x + H t))
      (hρm.comp (measurable_snd.add (hH.comp measurable_fst)))
    filter_upwards [] with t
    exact ⟨fun x => hρ0 _, hρi.comp_add_right _, by
      rw [integral_add_right_eq_self, hρ1]⟩
  have hFi := hi F hF
  have hGi := hi G hG
  have he := densityMixture_l1_le μ volume
    (fun t x => ρ (x + F t)) (fun t x => ρ (x + G t)) hFi hGi
  simp only [densityMixture, Real.norm_eq_abs] at he
  apply he.trans
  calc
    (∫ t, (∫ x, |ρ (x + F t) - ρ (x + G t)|) ∂μ) ≤ ∫ _, D * δ ∂μ := by
      apply integral_mono_ae (hFi.sub hGi).norm.integral_prod_left (integrable_const _)
      filter_upwards [hmove] with t ht
      exact (hρ _ _).trans (mul_le_mul_of_nonneg_left ht hD)
    _ = D * δ := by simp

end Erdos3

end

end OAI
