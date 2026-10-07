/- Modified for ProveIt: construct the mapped probability-measure instance
explicitly from measurability in Mathlib v4.32.0. Statements unchanged. -/
import OAI.Combinatorics.Progressions.Geometry.BoxImageComparison
import OAI.Combinatorics.Progressions.Geometry.TwoBoxSmoothingComplex
import OAI.Combinatorics.Progressions.Probability.PairedProductDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem realDensityMeasure_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℝ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, f x * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]

theorem realDensityMeasure_finite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    IsFiniteMeasure (realDensityMeasure μ f) := by
  constructor
  rw [realDensityMeasure_apply μ f hf hf0 MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top

theorem realDensityMeasure_real_univ {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    (realDensityMeasure μ f).real Set.univ = ∫ x, f x ∂μ := by
  change (realDensityMeasure μ f Set.univ).toReal = _
  rw [realDensityMeasure_apply μ f hf hf0 MeasurableSet.univ, Measure.restrict_univ,
    ENNReal.toReal_ofReal (integral_nonneg hf0)]

theorem mappedTest_eq_density {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ν : Measure X) (U : Ω → X) (hU : Measurable U)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hmap : Measure.map U μ = realDensityMeasure ν f)
    (φ : X → ℝ) (hφ : Measurable φ) : mappedTest μ U φ = ∫ x, f x * φ x ∂ν := by
  change (∫ a, φ (U a) ∂μ) = _
  rw [← integral_map hU.aemeasurable hφ.aestronglyMeasurable, hmap,
    realDensityMeasure_integral ν f hf hf0]

theorem imageTranslationBound_of_density {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (U : Ω → (ι → ℝ)) (hU : Measurable U)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f) (hfi : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    (hmap : Measure.map U μ = realDensityMeasure volume f) (H : ℝ≥0)
    (hmove : ∀ z, (∫ x, |f (x - z) - f x|) ≤ H * dist z 0) : ImageTranslationBound μ U H := by
  intro φ hφ hbound z
  have hshiftMeas : Measurable (fun x : ι → ℝ => φ (x + z)) :=
    hφ.comp (measurable_id.add_const z)
  rw [mappedTest_eq_density μ volume U hU f hf hf0 hmap
    (fun x => φ (x + z)) hshiftMeas, mappedTest_eq_density μ volume U hU f hf hf0 hmap φ hφ]
  have hshift := integral_add_right_eq_self (μ := volume) (fun x => f (x - z) * φ x) z
  simp only [add_sub_cancel_right] at hshift
  rw [hshift]
  have hi₁ : Integrable (fun x => f (x - z) * φ x) :=
    (hfi.comp_sub_right z).mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hi₂ : Integrable (fun x => f x * φ x) :=
    hfi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [← integral_sub hi₁ hi₂]
  have hd : Integrable (fun x => |f (x - z) - f x|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hfi.comp_sub_right z).sub hfi).norm
  have hp (x : ι → ℝ) : ‖f (x - z) * φ x - f x * φ x‖ ≤ |f (x - z) - f x| := by
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le hd (Filter.Eventually.of_forall hp)
  rw [Real.norm_eq_abs] at h
  exact h.trans (hmove z)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal Classical

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

noncomputable def fixedSpatialBlockDensity
    (μ : Measure T) (center : X → ℝ) (rest : T → X → ℝ)
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) : (X → ℝ) → ℝ :=
  haarShiftDensity μ (fun t => center + rest t)
    (twoBoxDifferenceDensity (fun _ => 1) (fun _ => 1)
      (A.trans (ContinuousLinearEquiv.neg ℝ)) B)

noncomputable def fixedSpatialBlockDensityCap
    (B : (X → ℝ) ≃L[ℝ] (X → ℝ)) : ℝ≥0 :=
  linearBoxDensityCap (fun _ => 1) (fun _ => zero_lt_one) B

noncomputable def fixedSpatialBlockDensityLipschitz
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) : ℝ≥0 :=
  (fixedSpatialBlockDensityCap B *
    boxWindowTranslationBound (fun _ : X => 1) (fun _ => zero_lt_one)) *
    ‖(A.trans (ContinuousLinearEquiv.neg ℝ)).symm.toContinuousLinearMap‖₊

private theorem fixedSpatialBlockKernel_lipschitz
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    LipschitzWith (fixedSpatialBlockDensityLipschitz A B)
      (twoBoxDifferenceDensity (fun _ => 1) (fun _ => 1)
        (A.trans (ContinuousLinearEquiv.neg ℝ)) B) :=
  twoBoxDifferenceDensity_lipschitz _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _

theorem fixedSpatialBlockDensity_measurable
    (μ : Measure T) [SFinite μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    Measurable (fixedSpatialBlockDensity μ center rest A B) :=
  haarShiftDensity_measurable μ (measurable_const.add hrest)
    (fixedSpatialBlockKernel_lipschitz A B).continuous.measurable

theorem fixedSpatialBlockDensity_bounds
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (∀ x, fixedSpatialBlockDensity μ center rest A B x ∈
      Set.Icc (0 : ℝ) (fixedSpatialBlockDensityCap B)) ∧
      LipschitzWith (fixedSpatialBlockDensityLipschitz A B)
        (fixedSpatialBlockDensity μ center rest A B) := by
  let f := twoBoxDifferenceDensity (fun _ : X => 1) (fun _ => 1)
    (A.trans (ContinuousLinearEquiv.neg ℝ)) B
  have hf : LipschitzWith (fixedSpatialBlockDensityLipschitz A B) f :=
    fixedSpatialBlockKernel_lipschitz A B
  have hc (x : X → ℝ) : f x ∈ Set.Icc (0 : ℝ) (fixedSpatialBlockDensityCap B) :=
    twoBoxDifferenceDensity_mem_Icc _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _ x
  apply densityMixture_uniform_bound μ (fun t x => f (x - (center + rest t)))
    (fixedSpatialBlockDensityCap B) (fixedSpatialBlockDensityLipschitz A B)
  · intro x
    exact (hf.continuous.measurable.comp
      (measurable_const.sub (measurable_const.add hrest))).aestronglyMeasurable
  · exact ae_of_all μ (fun t => ⟨fun x => hc _, by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_sub_right] using hf.dist_le_mul
        (x - (center + rest t)) (y - (center + rest t))⟩)

theorem fixedSpatialBlockDensity_probability_density
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (∀ x, 0 ≤ fixedSpatialBlockDensity μ center rest A B x) ∧
      Integrable (fixedSpatialBlockDensity μ center rest A B) ∧
      (∫ x, fixedSpatialBlockDensity μ center rest A B x) = 1 := by
  apply haarShiftDensity_probability volume μ (measurable_const.add hrest)
    (fixedSpatialBlockKernel_lipschitz A B).continuous.measurable
    (twoBoxDifferenceDensity_integrable _ _ _ _)
  · intro x
    exact (twoBoxDifferenceDensity_mem_Icc _ _ (fun _ => zero_lt_one)
      (fun _ => zero_lt_one) _ _ x).1
  · exact twoBoxDifferenceDensity_mass _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _

theorem fixedSpatialBlockDensity_probability
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    IsProbabilityMeasure (realDensityMeasure volume (fixedSpatialBlockDensity μ center rest A B)) := by
  have hp := fixedSpatialBlockDensity_probability_density μ center hrest A B
  exact realDensityMeasure_probability volume _ hp.2.1 hp.1 hp.2.2

theorem fixedSpatialBlockDensity_real_test_integral
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ))
    (φ : (X → ℝ) → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, fixedSpatialBlockDensity μ center rest A B x * φ x) =
      ∫ t, ∫ u, boxProbabilityWindow (fun _ : X => 1) 0 u *
        ∫ v, boxProbabilityWindow (fun _ : X => 1) 0 v *
          φ (center + A u + B v + rest t) ∂volume ∂volume ∂μ := by
  have hf := fixedSpatialBlockKernel_lipschitz A B
  have hi := twoBoxDifferenceDensity_integrable (fun _ : X => 1) (fun _ => 1)
    (A.trans (ContinuousLinearEquiv.neg ℝ)) B
  have h0 (x : X → ℝ) : 0 ≤ twoBoxDifferenceDensity (fun _ : X => 1) (fun _ => 1)
      (A.trans (ContinuousLinearEquiv.neg ℝ)) B x :=
    (twoBoxDifferenceDensity_mem_Icc _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _ x).1
  have hm := twoBoxDifferenceDensity_mass (fun _ : X => 1) (fun _ => 1)
    (fun _ => zero_lt_one) (fun _ => zero_lt_one) (A.trans (ContinuousLinearEquiv.neg ℝ)) B
  change (∫ x, haarShiftDensity μ (fun t => center + rest t) _ x * φ x) = _
  rw [haarShiftDensity_test_integral volume μ (z := fun t => center + rest t)
    (measurable_const.add hrest)
    hf.continuous.measurable hi h0 hm φ hφ hbound]
  apply integral_congr_ae
  exact ae_of_all μ (fun t => by
    have he (u v : X → ℝ) :
        B v - (A.trans (ContinuousLinearEquiv.neg ℝ)) u + (center + rest t) =
          center + A u + B v + rest t := by
      simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.neg_apply,
        sub_neg_eq_add]
      abel
    simpa only [he] using twoBoxDifferenceDensity_test_integral (fun _ : X => 1)
      (fun _ => 1) (A.trans (ContinuousLinearEquiv.neg ℝ)) B
      (fun y => φ (y + (center + rest t)))
      (hφ.comp (measurable_id.add measurable_const)) (fun y => hbound _))

theorem fixedSpatialBlockDensity_complex_test_integral
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ))
    (φ : (X → ℝ) → ℂ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, (fixedSpatialBlockDensity μ center rest A B x : ℂ) * φ x) =
      ∫ t, ∫ u, (boxProbabilityWindow (fun _ : X => 1) 0 u : ℂ) *
        ∫ v, (boxProbabilityWindow (fun _ : X => 1) 0 v : ℂ) *
          φ (center + A u + B v + rest t) ∂volume ∂volume ∂μ := by
  have hf := fixedSpatialBlockKernel_lipschitz A B
  have hi := twoBoxDifferenceDensity_integrable (fun _ : X => 1) (fun _ => 1)
    (A.trans (ContinuousLinearEquiv.neg ℝ)) B
  have h0 (x : X → ℝ) : 0 ≤ twoBoxDifferenceDensity (fun _ : X => 1) (fun _ => 1)
      (A.trans (ContinuousLinearEquiv.neg ℝ)) B x :=
    (twoBoxDifferenceDensity_mem_Icc _ _ (fun _ => zero_lt_one) (fun _ => zero_lt_one) _ _ x).1
  have hm := twoBoxDifferenceDensity_mass (fun _ : X => 1) (fun _ => 1)
    (fun _ => zero_lt_one) (fun _ => zero_lt_one) (A.trans (ContinuousLinearEquiv.neg ℝ)) B
  change (∫ x, (haarShiftDensity μ (fun t => center + rest t) _ x : ℂ) * φ x) = _
  rw [haarShiftDensity_test_integral_complex volume μ (z := fun t => center + rest t)
    (measurable_const.add hrest)
    hf.continuous.measurable hi h0 hm φ hφ hbound]
  apply integral_congr_ae
  exact ae_of_all μ (fun t => by
    have he (u v : X → ℝ) :
        B v - (A.trans (ContinuousLinearEquiv.neg ℝ)) u + (center + rest t) =
          center + A u + B v + rest t := by
      simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.neg_apply,
        sub_neg_eq_add]
      abel
    simpa only [he] using twoBoxDifferenceDensity_complex_test_integral (fun _ : X => 1)
      (fun _ => 1) (A.trans (ContinuousLinearEquiv.neg ℝ)) B
      (fun y => φ (y + (center + rest t)))
      (hφ.comp (measurable_id.add measurable_const)) (fun y => hbound _))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem boundedDensity_mass {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hB : ∀ x, f x ≤ B)
    [IsProbabilityMeasure (realDensityMeasure μ f)] : Integrable f μ ∧ (∫ x, f x ∂μ) = 1 := by
  have hi : Integrable f μ := (integrable_const B).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hB x))
  refine ⟨hi, ?_⟩
  have he := realDensityMeasure_real_univ μ f hi hf0
  change ((realDensityMeasure μ f) Set.univ).toReal = _ at he
  rw [measure_univ, ENNReal.toReal_one] at he
  exact he.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem density_l1_le_of_bounded_tests {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) {ε : ℝ}
    (he : ∀ φ : X → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      |(∫ x, f x*φ x ∂μ)-(∫ x, g x*φ x ∂μ)| ≤ ε) :
    (∫ x, |f x-g x| ∂μ) ≤ ε := by
  let φ := fun x => if 0 ≤ f x-g x then (1 : ℝ) else -1
  have hφ : Measurable φ := Measurable.ite (measurableSet_le measurable_const (hf.sub hg))
    measurable_const measurable_const
  have hbound : ∀ x, ‖φ x‖ ≤ 1 := by
    intro x
    dsimp [φ]
    split_ifs <;> norm_num
  have hif := hfi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hig := hgi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hid : (∫ x, f x*φ x ∂μ)-(∫ x, g x*φ x ∂μ) = ∫ x, |f x-g x| ∂μ := by
    rw [← integral_sub hif hig]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← sub_mul]
    dsimp [φ]
    split_ifs with hx
    · rw [mul_one, abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      ring
  have h := he φ hφ hbound
  rw [hid, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at h
  exact h

theorem imageComparison_density_l1 {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ν : Measure X) (U V : Ω → X) (hU : Measurable U) (hV : Measurable V)
    (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f ν) (hgi : Integrable g ν) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hUf : μ.map U = realDensityMeasure ν f) (hVg : μ.map V = realDensityMeasure ν g) {ε : ℝ}
    (he : ∀ φ : X → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      |mappedTest μ U φ-mappedTest μ V φ| ≤ ε) : (∫ x, |f x-g x| ∂ν) ≤ ε := by
  apply density_l1_le_of_bounded_tests ν f g hf hg hfi hgi
  intro φ hφ hbound
  have h := he φ hφ hbound
  rw [mappedTest_eq_density μ ν U hU f hf hf0 hUf φ hφ,
    mappedTest_eq_density μ ν V hV g hg hg0 hVg φ hφ] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem realDensityMeasure_mul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) :
    realDensityMeasure (realDensityMeasure μ f) g = realDensityMeasure μ (fun x => f x * g x) := by
  unfold realDensityMeasure
  rw [← withDensity_mul μ hf.ennreal_ofReal hg.ennreal_ofReal]
  congr 1
  funext x
  exact (ENNReal.ofReal_mul (hf0 x)).symm

theorem ae_realDensityMeasure_of_forall_nonzero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (P : X → Prop)
    (hP : ∀ x, f x ≠ 0 → P x) : ∀ᵐ x ∂realDensityMeasure μ f, P x := by
  apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
  filter_upwards [] with x hx
  apply hP x
  intro hzero
  simp only [hzero, ENNReal.ofReal_zero, ne_eq, not_true_eq_false] at hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X]

theorem fixedSpatialBlockDensityCap_eq
    (B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (fixedSpatialBlockDensityCap B : ℝ) = inverseJacobian B := by
  change inverseJacobian B * (∏ _ : X, (1 : ℝ) / 1) = inverseJacobian B
  simp

theorem fixedSpatialNegBlock_inverse_norm
    (A : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    ‖(A.trans (ContinuousLinearEquiv.neg ℝ)).symm.toContinuousLinearMap‖₊ =
      ‖A.symm.toContinuousLinearMap‖₊ := by
  have he : (A.trans (ContinuousLinearEquiv.neg ℝ)).symm.toContinuousLinearMap =
      -A.symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    change A.symm (-x) = -(A.symm x)
    exact map_neg A.symm x
  rw [he, nnnorm_neg]

theorem fixedSpatialBlockDensityLipschitz_eq
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (fixedSpatialBlockDensityLipschitz A B : ℝ) =
      2 * Fintype.card X * inverseJacobian B * ‖A.symm.toContinuousLinearMap‖ := by
  unfold fixedSpatialBlockDensityLipschitz
  rw [fixedSpatialNegBlock_inverse_norm]
  simp only [NNReal.coe_mul, fixedSpatialBlockDensityCap_eq, coe_nnnorm]
  change inverseJacobian B * (∑ _ : X, (2 : ℝ) / 1) * _ = _
  simp only [div_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

variable [DecidableEq X]

theorem fixedSpatialBlockDensity_bounds_of_inverseBounds
    {T : Type*} [MeasurableSpace T] (μ : Measure T) [IsProbabilityMeasure μ]
    (center : X → ℝ) {rest : T → X → ℝ} (hrest : Measurable rest)
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) (CJ KA : ℝ≥0)
    (hJ : inverseJacobian B ≤ CJ) (hA : ‖A.symm.toContinuousLinearMap‖ ≤ KA) :
    (∀ x, fixedSpatialBlockDensity μ center rest A B x ∈ Set.Icc (0 : ℝ) CJ) ∧
      LipschitzWith (2 * Fintype.card X * CJ * KA)
        (fixedSpatialBlockDensity μ center rest A B) := by
  have hb := fixedSpatialBlockDensity_bounds μ center hrest A B
  constructor
  · intro x
    refine ⟨(hb.1 x).1, (hb.1 x).2.trans ?_⟩
    simpa only [fixedSpatialBlockDensityCap_eq] using hJ
  · apply hb.2.weaken
    apply NNReal.coe_le_coe.mp
    rw [fixedSpatialBlockDensityLipschitz_eq]
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hJ (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      hA (norm_nonneg _) (by positivity)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical ENNReal

theorem boxProbabilityWindow_one_eq_indicator (X : Type*) [Fintype X] :
    boxProbabilityWindow (fun _ : X => 1) 0 =
      (positiveUnitBox X).indicator (fun _ => (1 : ℝ)) := by
  funext u
  by_cases hu : u ∈ positiveUnitBox X
  · rw [Set.indicator_of_mem hu]
    simp only [boxProbabilityWindow, normalizedIntervalWindow, Pi.zero_apply,
      zero_add, div_one, intervalWindow]
    simp only [Set.indicator_of_mem (hu _ (Set.mem_univ _)), Finset.prod_const_one]
  · rw [Set.indicator_of_notMem hu]
    have he : ∃ i, u i ∉ Set.Ioc (0 : ℝ) 1 := by
      simpa only [positiveUnitBox, Set.mem_pi, Set.mem_univ, forall_const, not_forall] using hu
    obtain ⟨i, hi⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [normalizedIntervalWindow, Pi.zero_apply, zero_add, div_one,
      intervalWindow, Set.indicator_of_notMem hi]

theorem unitBoxMeasure_eq_boxWindowDensity (X : Type*) [Fintype X] :
    unitBoxMeasure X = realDensityMeasure volume (boxProbabilityWindow (fun _ : X => 1) 0) := by
  rw [boxProbabilityWindow_one_eq_indicator]
  change volume.restrict (positiveUnitBox X) =
    volume.withDensity (fun u => ENNReal.ofReal ((positiveUnitBox X).indicator (fun _ => (1 : ℝ)) u))
  have he : (fun u => ENNReal.ofReal ((positiveUnitBox X).indicator (fun _ => (1 : ℝ)) u)) =
      (positiveUnitBox X).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext u
    by_cases hu : u ∈ positiveUnitBox X <;> simp [hu]
  rw [he]
  exact (withDensity_indicator_one (μ := volume) (positiveUnitBox_measurable (ι := X))).symm

theorem unitBoxMeasure_real_integral {X : Type*} [Fintype X] (φ : (X → ℝ) → ℝ) :
    (∫ u, φ u ∂unitBoxMeasure X) =
      ∫ u, boxProbabilityWindow (fun _ : X => 1) 0 u * φ u := by
  rw [unitBoxMeasure_eq_boxWindowDensity,
    realDensityMeasure_integral volume _ (boxProbabilityWindow_measurable _ _)
      (boxProbabilityWindow_nonneg _ (fun _ => zero_lt_one) _)]

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

theorem fixedSpatialBlockDensity_mapped_real_integral
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ))
    (φ : (X → ℝ) → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ p, φ (center + A p.2.1 + B p.2.2 + rest p.1)
      ∂μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))) =
        ∫ y, fixedSpatialBlockDensity μ center rest A B y * φ y := by
  have hmap : Measurable (fun p : T × ((X → ℝ) × (X → ℝ)) =>
      center + A p.2.1 + B p.2.2 + rest p.1) := by
    fun_prop
  have hi : Integrable (fun p => φ (center + A p.2.1 + B p.2.2 + rest p.1))
      (μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))) :=
    (integrable_const C).mono' (hφ.comp hmap).aestronglyMeasurable
      (ae_of_all _ (fun p => hbound _))
  rw [integral_prod _ hi, fixedSpatialBlockDensity_real_test_integral μ center hrest A B φ hφ hbound]
  apply integral_congr_ae
  filter_upwards [] with t
  have hit : Integrable (fun p : (X → ℝ) × (X → ℝ) =>
      φ (center + A p.1 + B p.2 + rest t)) ((unitBoxMeasure X).prod (unitBoxMeasure X)) :=
    (integrable_const C).mono'
      (hφ.comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ (fun p => hbound _))
  rw [integral_prod _ hit, unitBoxMeasure_real_integral]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [unitBoxMeasure_real_integral]

theorem fixedSpatialBlockDensity_image_law
    (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
    (hrest : Measurable rest) (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) :
    (μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))).map
        (fun p => center + A p.2.1 + B p.2.2 + rest p.1) =
      realDensityMeasure volume (fixedSpatialBlockDensity μ center rest A B) := by
  let source := μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))
  let U := fun p : T × ((X → ℝ) × (X → ℝ)) => center + A p.2.1 + B p.2.2 + rest p.1
  have hU : Measurable U := by fun_prop
  let : IsProbabilityMeasure (source.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  let := fixedSpatialBlockDensity_probability μ center hrest A B
  change source.map U = _
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hb : ∀ x, ‖s.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  have ht := fixedSpatialBlockDensity_mapped_real_integral μ center hrest A B
    (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs) hb
  change (∫ p, s.indicator (fun _ => (1 : ℝ)) (U p) ∂source) = _ at ht
  rw [← integral_map hU.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable,
    ← realDensityMeasure_integral volume _ (fixedSpatialBlockDensity_measurable μ center hrest A B)
      (fixedSpatialBlockDensity_probability_density μ center hrest A B).1] at ht
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem coordinateScaleEquiv_det (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) :
    LinearMap.det (coordinateScaleEquiv d hd).toLinearMap = ∏ i, d i :=
  diagonalDensityTransport_det d hd

noncomputable def diagonalImageDensity (d : ι → ℝ)
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  (∏ i, |d i|)⁻¹ * f (fun i => x i / d i)

theorem diagonalImageDensity_eq_pullback (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (f : (ι → ℝ) → ℝ) :
    diagonalImageDensity d f =
      linearDensityPullback (coordinateScaleEquiv d hd).toContinuousLinearEquiv f := by
  funext x
  simpa only [diagonalImageDensity, diagonalDensityTransport, Finset.abs_prod] using
    (diagonalDensityTransport_eq d hd f x).symm

theorem diagonalImageDensity_measurable (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) : Measurable (diagonalImageDensity d f) := by
  rw [diagonalImageDensity_eq_pullback d hd]
  exact linearDensityPullback_measurable _ hf

theorem diagonalImageDensity_nonneg (d : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ι → ℝ) :
    0 ≤ diagonalImageDensity d f x :=
  mul_nonneg (inv_nonneg.mpr (Finset.prod_nonneg (fun i _ => abs_nonneg (d i)))) (hf _)

theorem diagonalImageDensity_integrable (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) : Integrable (diagonalImageDensity d f) := by
  rw [diagonalImageDensity_eq_pullback d hd]
  exact linearDensityPullback_integrable _ hf

theorem diagonalImageDensity_integral (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (f : (ι → ℝ) → ℝ) : (∫ x, diagonalImageDensity d f x) = ∫ x, f x := by
  rw [diagonalImageDensity_eq_pullback d hd]
  exact linearDensityPullback_integral _ f

theorem diagonalImageDensity_test_integral (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (f φ : (ι → ℝ) → ℝ) :
    (∫ x, diagonalImageDensity d f x * φ x) = ∫ x, f x * φ (fun i => d i * x i) := by
  rw [diagonalImageDensity_eq_pullback d hd]
  exact linearDensityPullback_test_integral _ f φ

theorem diagonalImageDensity_l1_le_of_tests (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (f g : (ι → ℝ) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g) {ε : ℝ}
    (he : ∀ φ : (ι → ℝ) → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      |(∫ x, f x * φ (fun i => d i * x i)) - (∫ x, g x * φ x)| ≤ ε) :
    (∫ x, |diagonalImageDensity d f x - g x|) ≤ ε := by
  apply density_l1_le_of_bounded_tests volume _ g
    (diagonalImageDensity_measurable d hd hf) hg
    (diagonalImageDensity_integrable d hd hfi) hgi
  intro φ hφ hφb
  rw [diagonalImageDensity_test_integral d hd]
  exact he φ hφ hφb

end Erdos3

end

end OAI
