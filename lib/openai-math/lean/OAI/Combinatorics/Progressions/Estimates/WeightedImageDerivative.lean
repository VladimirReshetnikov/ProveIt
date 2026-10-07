import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import OAI.Combinatorics.Progressions.Geometry.DivergenceSupport
import OAI.Combinatorics.Progressions.Probability.BoundedSmoothTestDensity
import OAI.Combinatorics.Progressions.Probability.DiagonalImageDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

theorem integral_unit_test_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ)
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem integral_test_difference_le_l1 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ ∫ x, ‖f x - g x‖ ∂μ := by
  rw [← integral_sub hf hg, ← Real.norm_eq_abs]
  exact norm_integral_le_integral_norm _

theorem bounded_test_comparison_of_smooth {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : ℝ}
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → (∀ x, ‖g x‖ ≤ 1) →
      |(∫ x, g x ∂μ) - ∫ x, g x ∂ν| ≤ C)
    (f : E → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g, hgc, hgs, hgb, _, herr⟩ := exists_smooth_unit_test_l1 (μ + ν) f hf hbound hε
  have hfμ := integral_unit_test_integrable μ f hf hbound
  have hfν := integral_unit_test_integrable ν f hf hbound
  have hgμ := integral_unit_test_integrable μ g hgc.continuous.measurable hgb
  have hgν := integral_unit_test_integrable ν g hgc.continuous.measurable hgb
  have hμ := integral_test_difference_le_l1 μ f g hfμ hgμ
  have hν := integral_test_difference_le_l1 ν f g hfν hgν
  have hdiffμ : Integrable (fun x => ‖f x - g x‖) μ := (hfμ.sub hgμ).norm
  have hdiffν : Integrable (fun x => ‖f x - g x‖) ν := (hfν.sub hgν).norm
  rw [integral_add_measure hdiffμ hdiffν] at herr
  have hg := h g hgc hgs hgb
  have htri := abs_sub_le (∫ x, f x ∂μ) (∫ x, g x ∂μ) (∫ x, f x ∂ν)
  have htri' := abs_sub_le (∫ x, g x ∂μ) (∫ x, g x ∂ν) (∫ x, f x ∂ν)
  rw [abs_sub_comm (∫ x, g x ∂ν) (∫ x, f x ∂ν)] at htri'
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem smooth_translated_integral_hasDerivAt (μ : Measure E) [IsFiniteMeasure μ]
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (hbound : ∀ x, ‖φ x‖ ≤ 1) (z : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, φ (x + t • z) ∂μ)
      (∫ x, fderiv ℝ φ (x + t • z) z ∂μ) t := by
  have hdc := hφ.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous hdc
  have hline (x : E) (s : ℝ) : HasDerivAt (fun t : ℝ => φ (x + t • z))
      (fderiv ℝ φ (x + s • z) z) s := by
    have hz : HasDerivAt (fun t : ℝ => x + t • z) z s := by
      have h := ((hasDerivAt_id s).smul_const z).const_add x
      simp only [one_smul, id_eq] at h
      exact h
    exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s hz
  have hmeas (s : ℝ) : Measurable (fun x : E => φ (x + s • z)) :=
    hφ.continuous.measurable.comp (measurable_id.add_const _)
  have hderivMeas : AEStronglyMeasurable (fun x : E => fderiv ℝ φ (x + t • z) z) μ :=
    ((hdc.comp (continuous_id.add continuous_const)).clm_apply continuous_const).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (bound := fun _ : E => K * ‖z‖) Filter.univ_mem
    (Filter.Eventually.of_forall (fun s => (hmeas s).aestronglyMeasurable))
    (integral_unit_test_integrable μ _ (hmeas t) (fun x => hbound _)) hderivMeas
    (Filter.Eventually.of_forall (fun x s _ =>
      ((fderiv ℝ φ (x + s • z)).le_opNorm z).trans
        (mul_le_mul_of_nonneg_right (hK _) (norm_nonneg z))))
    (integrable_const _) (Filter.Eventually.of_forall (fun x s _ => hline x s))).2

theorem smooth_translation_bound_of_weak_derivative (μ : Measure E) [IsFiniteMeasure μ]
    (z : E) (D : ℝ)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ x, ‖ψ x‖ ≤ 1) →
      |∫ x, fderiv ℝ ψ x z ∂μ| ≤ D)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, φ (x + z) ∂μ) - ∫ x, φ x ∂μ| ≤ D := by
  have hd (t : ℝ) := smooth_translated_integral_hasDerivAt μ φ hφ hs hbound z t
  have hb (t : ℝ) : ‖∫ x, fderiv ℝ φ (x + t • z) z ∂μ‖ ≤ D := by
    have hc : ContDiff ℝ ∞ (fun x : E => φ (x + t • z)) :=
      hφ.comp (contDiff_id.add contDiff_const)
    have hsupport : HasCompactSupport (fun x : E => φ (x + t • z)) :=
      hs.comp_homeomorph (Homeomorph.addRight (t • z))
    have h := hweak _ hc hsupport (fun x => hbound _)
    simp only [fderiv_comp_add_right] at h
    exact h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := fun t : ℝ => ∫ x, φ (x + t • z) ∂μ)
    (f' := fun t : ℝ => ∫ x, fderiv ℝ φ (x + t • z) z ∂μ)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb t) convex_univ
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
  simpa only [one_smul, zero_smul, add_zero, sub_zero, norm_one, mul_one, Real.norm_eq_abs] using h

theorem translation_bound_of_weak_derivative [FiniteDimensional ℝ E] (μ : Measure E) [IsFiniteMeasure μ]
    (z : E) (D : ℝ)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ x, ‖ψ x‖ ≤ 1) →
      |∫ x, fderiv ℝ ψ x z ∂μ| ≤ D)
    (φ : E → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, φ (x + z) ∂μ) - ∫ x, φ x ∂μ| ≤ D := by
  have hm : Measurable (fun x : E => x + z) := measurable_id.add_const z
  have h := bounded_test_comparison_of_smooth (Measure.map (fun x => x + z) μ) μ (C := D)
    (fun ψ hc hs hb => by
      rw [integral_map hm.aemeasurable hc.continuous.aestronglyMeasurable]
      exact smooth_translation_bound_of_weak_derivative μ z D hweak ψ hc hs hb) φ hφ hbound
  rw [integral_map hm.aemeasurable hφ.aestronglyMeasurable] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

theorem imageTranslationBound_of_smooth_derivative {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U) (H : ℝ≥0)
    (hweak : ∀ (ψ : (ι → ℝ) → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ x, ‖ψ x‖ ≤ 1) → ∀ z,
      |∫ a, fderiv ℝ ψ (U a) z ∂μ| ≤ H * dist z 0) : ImageTranslationBound μ U H := by
  intro φ hφ hbound z
  have h := translation_bound_of_weak_derivative (Measure.map U μ) z ((H : ℝ) * dist z 0)
    (fun ψ hc hs hb => by
      have hm : Measurable (fun x => fderiv ℝ ψ x z) :=
        ((hc.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
      rw [integral_map hU.aemeasurable hm.aestronglyMeasurable]
      exact hweak ψ hc hs hb z) φ hφ hbound
  have hm : Measurable (fun x : ι → ℝ => φ (x + z)) :=
    hφ.comp (measurable_id.add_const z)
  rw [integral_map hU.aemeasurable hm.aestronglyMeasurable,
    integral_map hU.aemeasurable hφ.aestronglyMeasurable] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

theorem weighted_image_derivative_identity
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 1 U) (w : (κ → ℝ) → ℝ)
    (Q : κ → (κ → ℝ) → ℝ) (hQ : ∀ j, ContDiff ℝ 1 (Q j))
    (hs : ∀ j, HasCompactSupport (Q j)) (z : ι → ℝ)
    (hcolumn : ∀ x, fderiv ℝ U x (fun j => Q j x) = w x • z)
    (φ : (ι → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) :
    (∫ x, w x * fderiv ℝ φ (U x) z) = -∫ x, coordinateDivergence Q x * φ (U x) := by
  have hpoint (x : κ → ℝ) : fderiv ℝ (fun x => φ (U x)) x (fun j => Q j x) =
      w x * fderiv ℝ φ (U x) z := by
    change fderiv ℝ (φ ∘ U) x (fun j => Q j x) = _
    rw [fderiv_comp x (hφ.differentiable (by norm_num) _) (hU.differentiable (by norm_num) _),
      ContinuousLinearMap.comp_apply, hcolumn, map_smul, smul_eq_mul]
  have h := coordinate_vectorField_integration_by_parts Q hQ hs (fun x => φ (U x)) (hφ.comp hU)
  simpa only [hpoint] using h

theorem weighted_image_derivative_bound
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 1 U)
    (w : (κ → ℝ) → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (Q : κ → (κ → ℝ) → ℝ) (hQ : ∀ j, ContDiff ℝ 1 (Q j))
    (hs : ∀ j, HasCompactSupport (Q j)) (z : ι → ℝ)
    (hcolumn : ∀ x, fderiv ℝ U x (fun j => Q j x) = w x • z)
    {B : ℝ} (hdiv : (∫ x, |coordinateDivergence Q x|) ≤ B)
    (φ : (ι → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |∫ x, fderiv ℝ φ (U x) z ∂realDensityMeasure volume w| ≤ B := by
  rw [realDensityMeasure_integral volume w hw hw0,
    weighted_image_derivative_identity U hU w Q hQ hs z hcolumn φ hφ, abs_neg]
  have hi : Integrable (fun x => |coordinateDivergence Q x|) := by
    have hint : Integrable (coordinateDivergence Q) volume :=
      (coordinateDivergence_continuous Q hQ).integrable_of_hasCompactSupport
        (coordinateDivergence_hasCompactSupport Q hs)
    have h := hint.norm
    simp only [Real.norm_eq_abs] at h
    exact h
  have hp (x : κ → ℝ) : ‖coordinateDivergence Q x * φ (U x)‖ ≤ |coordinateDivergence Q x| := by
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg _)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hp)
  rw [Real.norm_eq_abs] at h
  exact h.trans hdiv

end Erdos3

end

end OAI
