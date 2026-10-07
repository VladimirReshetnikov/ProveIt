/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import OAI.Combinatorics.Progressions.Probability.SelectedDensityNormalization

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

noncomputable def affineProbabilityProfile (c w x : ℝ) : ℝ :=
  w⁻¹ * smoothProbabilityProfile ((x - c) / w)

theorem affineProbabilityProfile_nonneg (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ) :
    0 ≤ affineProbabilityProfile c w x :=
  mul_nonneg (inv_nonneg.mpr hw.le) (smoothProbabilityProfile_range _).1

theorem affineProbabilityProfile_le (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ) :
    affineProbabilityProfile c w x ≤ w⁻¹ := by
  exact (mul_le_mul_of_nonneg_left (smoothProbabilityProfile_range _).2
    (inv_nonneg.mpr hw.le)).trans_eq (mul_one _)

theorem affineProbabilityProfile_contDiff (c w : ℝ) :
    ContDiff ℝ ∞ (affineProbabilityProfile c w) := by
  change ContDiff ℝ ∞ (fun x => w⁻¹ * smoothProbabilityProfile ((x-c)/w))
  exact contDiff_const.mul
    (smoothProbabilityProfile_contDiff.comp ((contDiff_id.sub contDiff_const).div_const w))

theorem affineProbabilityProfile_zero (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ)
    (hx : w < |x - c|) : affineProbabilityProfile c w x = 0 := by
  have hnorm : 1 < |(x-c)/w| := by
    rw [abs_div, abs_of_pos hw]
    exact (one_lt_div hw).mpr hx
  rw [affineProbabilityProfile, smoothProbabilityProfile_zero_outside _ hnorm, mul_zero]

theorem affineProbabilityProfile_zero_outside (c : ℝ) {w : ℝ} (hw : 0 < w) (x : ℝ)
    (hx : |c| + w < |x|) : affineProbabilityProfile c w x = 0 := by
  apply affineProbabilityProfile_zero c hw x
  have ht : |x| ≤ |x-c| + |c| := by
    simpa only [sub_add_cancel] using abs_add_le (x-c) c
  linarith

theorem affineProbabilityProfile_compact (c : ℝ) {w : ℝ} (hw : 0 < w) :
    HasCompactSupport (affineProbabilityProfile c w) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) (|c|+w))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact le_of_not_gt (fun h => hx (affineProbabilityProfile_zero_outside c hw x h))

theorem affineProbabilityProfile_integrable (c : ℝ) {w : ℝ} (hw : 0 < w) :
    Integrable (affineProbabilityProfile c w) :=
  (affineProbabilityProfile_contDiff c w).continuous.integrable_of_hasCompactSupport
    (affineProbabilityProfile_compact c hw)

theorem affineProbabilityProfile_integral (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ x, affineProbabilityProfile c w x) = 1 := by
  change (∫ x, w⁻¹ * smoothProbabilityProfile ((x-c)/w)) = 1
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x => smoothProbabilityProfile (x/w)) c,
    Measure.integral_comp_div, smoothProbabilityProfile_integral, smul_eq_mul,
    mul_one, abs_of_pos hw, inv_mul_cancel₀ hw.ne']

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

noncomputable def affineProductProfile {I : Type*} [Fintype I] (c w x : I → ℝ) : ℝ :=
  ∏ i, affineProbabilityProfile (c i) (w i) (x i)

noncomputable def profileWidthFactor {I : Type*} [Fintype I] (w : I → ℝ) : ℝ :=
  ∏ i, (w i)⁻¹

theorem affineProductProfile_eq {I : Type*} [Fintype I] (c w x : I → ℝ) :
    affineProductProfile c w x = profileWidthFactor w *
      smoothProductProfile I (fun i => (x i - c i) / w i) := by
  simp only [affineProductProfile, affineProbabilityProfile, Finset.prod_mul_distrib,
    profileWidthFactor, smoothProductProfile]

theorem profileWidthFactor_pos {I : Type*} [Fintype I] (w : I → ℝ) (hw : ∀ i, 0 < w i) :
    0 < profileWidthFactor w := Finset.prod_pos (fun i _ => inv_pos.mpr (hw i))

theorem affineProductProfile_nonneg {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) (x : I → ℝ) : 0 ≤ affineProductProfile c w x :=
  Finset.prod_nonneg (fun i _ => affineProbabilityProfile_nonneg (c i) (hw i) (x i))

theorem affineProductProfile_norm_le {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) (x : I → ℝ) : ‖affineProductProfile c w x‖ ≤ profileWidthFactor w := by
  rw [Real.norm_eq_abs, abs_of_nonneg (affineProductProfile_nonneg c w hw x)]
  exact Finset.prod_le_prod₀ (fun i _ => affineProbabilityProfile_nonneg (c i) (hw i) (x i))
    (fun i _ => affineProbabilityProfile_le (c i) (hw i) (x i))

theorem affineProductProfile_contDiff {I : Type*} [Fintype I] (c w : I → ℝ) :
    ContDiff ℝ ∞ (affineProductProfile c w) := by
  unfold affineProductProfile
  apply contDiff_prod
  intro i _
  exact (affineProbabilityProfile_contDiff (c i) (w i)).comp
    (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).contDiff

theorem affineProductProfile_compact {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : HasCompactSupport (affineProductProfile c w) :=
  tensorCutoffWeight_compact (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_compact (c i) (hw i))

theorem affineProductProfile_integrable {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : Integrable (affineProductProfile c w) :=
  (affineProductProfile_contDiff c w).continuous.integrable_of_hasCompactSupport
    (affineProductProfile_compact c w hw)

theorem affineProductProfile_integral {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : (∫ x, affineProductProfile c w x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun i => affineProbabilityProfile (c i) (w i)) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [affineProbabilityProfile_integral _ (hw _), Finset.prod_const_one]

theorem affineProductProfile_zero_outside {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) {R : ℝ} (hR : 0 ≤ R) (hcw : ∀ i, |c i| + w i ≤ R) :
    ∀ x, R < ‖x‖ → affineProductProfile c w x = 0 := by
  classical
  intro x hx
  by_contra hne
  apply (not_le_of_gt hx)
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_contra! hi
  exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
    (affineProbabilityProfile_zero_outside (c i) (hw i) (x i) ((hcw i).trans_lt hi)))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem affineProbabilityProfile_integral_test (c : ℝ) {w : ℝ} (hw : 0 < w) (φ : ℝ → ℝ) :
    (∫ x, affineProbabilityProfile c w x * φ x) =
      ∫ y, smoothProbabilityProfile y * φ (c + w*y) := by
  let g := fun y => smoothProbabilityProfile y * φ (c+w*y)
  have he (x : ℝ) : affineProbabilityProfile c w x * φ x = w⁻¹ * g ((x-c)/w) := by
    have hx : c + w*((x-c)/w) = x := by field_simp [hw.ne']; ring
    simp only [affineProbabilityProfile, g, hx]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x => g (x/w)) c,
    Measure.integral_comp_div, smul_eq_mul, abs_of_pos hw, ← mul_assoc,
    inv_mul_cancel₀ hw.ne', one_mul]

theorem affineProbabilityProfile_law (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (realDensityMeasure volume smoothProbabilityProfile).map (fun y => c + w*y) =
      realDensityMeasure volume (affineProbabilityProfile c w) := by
  have hψ : Integrable smoothProbabilityProfile :=
    smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport smoothProbabilityProfile_compact
  let : IsFiniteMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_finite _ _ hψ (fun y => (smoothProbabilityProfile_range y).1)
  let : IsFiniteMeasure (realDensityMeasure volume (affineProbabilityProfile c w)) :=
    realDensityMeasure_finite _ _ (affineProbabilityProfile_integrable c hw) (affineProbabilityProfile_nonneg c hw)
  have hmap : Measurable (fun y : ℝ => c+w*y) := by fun_prop
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [integral_map hmap.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral volume smoothProbabilityProfile
      smoothProbabilityProfile_contDiff.continuous.measurable (fun y => (smoothProbabilityProfile_range y).1),
    realDensityMeasure_integral volume (affineProbabilityProfile c w)
      (affineProbabilityProfile_contDiff c w).continuous.measurable (affineProbabilityProfile_nonneg c hw)]
  exact (affineProbabilityProfile_integral_test c hw φ).symm

theorem affineProductProfile_law {I : Type*} [Fintype I]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) :
    (realDensityMeasure volume (smoothProductProfile I)).map (fun y i => c i + w i * y i) =
      realDensityMeasure volume (affineProductProfile c w) := by
  have hψ : Integrable smoothProbabilityProfile :=
    smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport smoothProbabilityProfile_compact
  let : IsFiniteMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_finite _ _ hψ (fun y => (smoothProbabilityProfile_range y).1)
  have hsrc := realDensityMeasure_pi (fun _ : I => (volume : Measure ℝ))
    (fun _ => smoothProbabilityProfile) (fun _ => hψ) (fun _ y => (smoothProbabilityProfile_range y).1)
  have hdst := realDensityMeasure_pi (fun _ : I => (volume : Measure ℝ))
    (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_integrable (c i) (hw i))
    (fun i => affineProbabilityProfile_nonneg (c i) (hw i))
  change (Measure.pi (fun _ : I => realDensityMeasure volume smoothProbabilityProfile)) =
    realDensityMeasure volume (smoothProductProfile I) at hsrc
  change (Measure.pi (fun i : I => realDensityMeasure volume (affineProbabilityProfile (c i) (w i)))) =
    realDensityMeasure volume (affineProductProfile c w) at hdst
  rw [← hsrc, Measure.pi_map_pi (fun i =>
    (show Measurable (fun y : ℝ => c i + w i * y) by fun_prop).aemeasurable)]
  simp_rw [affineProbabilityProfile_law _ (hw _)]
  exact hdst

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem affineProbabilityProfile_support (c : ℝ) {w : ℝ} (hw : 0 < w) {x : ℝ}
    (hx : affineProbabilityProfile c w x ≠ 0) : |x - c| < 3 * w / 4 := by
  by_contra! h
  have hz : smoothProbabilityProfile ((x-c)/w) = 0 := by
    apply smoothProbabilityProfile_zero
    rw [abs_div, abs_of_pos hw]
    apply (le_div_iff₀ hw).mpr
    linarith
  exact hx (by simp only [affineProbabilityProfile, hz, mul_zero])

theorem realDensityMeasure_ae_of_support {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (P : X → Prop)
    (hP : ∀ x, f x ≠ 0 → P x) : ∀ᵐ x ∂realDensityMeasure μ f, P x := by
  apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
  exact Filter.Eventually.of_forall (fun x hx => hP x (fun hz => hx (by simp [hz])))

noncomputable def affineCoefficientMeasure (c w : ℝ) : Measure ℝ :=
  realDensityMeasure volume (affineProbabilityProfile c w)

theorem affineCoefficientMeasure_probability (c : ℝ) {w : ℝ} (hw : 0 < w) :
    IsProbabilityMeasure (affineCoefficientMeasure c w) :=
  realDensityMeasure_probability volume _ (affineProbabilityProfile_integrable c hw)
    (affineProbabilityProfile_nonneg c hw) (affineProbabilityProfile_integral c hw)

theorem affineCoefficientMeasure_support (c : ℝ) {w : ℝ} (hw : 0 < w) :
    ∀ᵐ x ∂affineCoefficientMeasure c w, |x - c| < 3 * w / 4 :=
  realDensityMeasure_ae_of_support volume _ (affineProbabilityProfile_contDiff c w).continuous.measurable
    _ (fun _ hx => affineProbabilityProfile_support c hw hx)

theorem affineCoefficientMeasure_law (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (realDensityMeasure volume smoothProbabilityProfile).map (fun y => c + w*y) =
      affineCoefficientMeasure c w :=
  affineProbabilityProfile_law c hw

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

theorem affineProductProfile_integral_test {J : Type*} [Fintype J]
    (c w : J → ℝ) (hw : ∀ j, 0 < w j) (φ : (J → ℝ) → ℝ) (hφ : Measurable φ) :
    (∫ x, affineProductProfile c w x * φ x) =
      ∫ r, smoothProductProfile J r * φ (fun j => c j + w j * r j) := by
  have hmap : Measurable (fun r : J → ℝ => fun j => c j + w j * r j) := by fun_prop
  rw [← realDensityMeasure_integral volume (affineProductProfile c w)
    (affineProductProfile_contDiff c w).continuous.measurable (affineProductProfile_nonneg c w hw),
    ← affineProductProfile_law c w hw, integral_map hmap.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral volume (smoothProductProfile J)
      (smoothProductProfile_contDiff J).continuous.measurable (fun r => (smoothProductProfile_range J r).1)]

theorem affineProductProfile_retained_integral {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) (c w : Ω → J → ℝ) (hw : ∀ ω j, 0 < w ω j)
    (φ : Ω → (J → ℝ) → ℝ) (hφ : ∀ ω, Measurable (φ ω)) :
    (∫ ω, (∫ x, affineProductProfile (c ω) (w ω) x * φ ω x) ∂μ) =
      ∫ ω, (∫ r, smoothProductProfile J r * φ ω (fun j => c ω j + w ω j * r j)) ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => affineProductProfile_integral_test (c ω) (w ω) (hw ω) (φ ω) (hφ ω))

theorem affineCoefficientDensity_unit_source {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (c w : J → ℝ) (hw : ∀ j, 0 < w j) :
    (realDensityMeasure volume (smoothProductProfile J)).map
      (fun r => normalizedIntegerColumns A S P *ᵥ (fun j => c j + w j * r j)) =
      realDensityMeasure volume
        (selectedCoefficientDensity A s hA S P hS hP (affineProductProfile c w)) := by
  have hF : Measurable (fun x => normalizedIntegerColumns A S P *ᵥ x) :=
    (matrixSupCLM (normalizedIntegerColumns A S P)).continuous.measurable
  have hmap : Measurable (fun r : J → ℝ => fun j => c j + w j * r j) := by fun_prop
  change ((realDensityMeasure volume (smoothProductProfile J)).map
    ((fun x => normalizedIntegerColumns A S P *ᵥ x) ∘
      (fun r j => c j + w j * r j))) = _
  rw [← Measure.map_map hF hmap, affineProductProfile_law c w hw]
  exact selectedCoefficientDensity_law A s hA S P hS hP _
    (affineProductProfile_integrable c w hw) (affineProductProfile_nonneg c w hw)

theorem affineProductProfile_measurable_comp {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (c w x : Ω → J → ℝ) (hc : Measurable c) (hw : Measurable w) (hx : Measurable x) :
    Measurable (fun ω => affineProductProfile (c ω) (w ω) (x ω)) := by
  unfold affineProductProfile affineProbabilityProfile
  apply Finset.measurable_prod
  intro j _
  exact ((measurable_pi_apply j).comp hw).inv.mul
    (smoothProbabilityProfile_contDiff.continuous.measurable.comp
      ((((measurable_pi_apply j).comp hx).sub ((measurable_pi_apply j).comp hc)).div
        ((measurable_pi_apply j).comp hw)))

end Erdos3

end

end OAI
