import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

section

namespace Erdos3

open MeasureTheory

def unitTestClip (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem unitTestClip_continuous : Continuous unitTestClip :=
  continuous_const.max (continuous_const.min continuous_id)

theorem unitTestClip_mem (x : ℝ) : unitTestClip x ∈ Set.Icc (-1 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem unitTestClip_zero : unitTestClip 0 = 0 := by norm_num [unitTestClip]

theorem unitTestClip_error {x : ℝ} (hx : |x| ≤ 1) (y : ℝ) :
    |x - unitTestClip y| ≤ |x - y| := by
  have hx' := abs_le.mp hx
  by_cases hy : y ≤ -1
  · have hmin : min 1 y = y := min_eq_right (by linarith)
    rw [unitTestClip, hmin, max_eq_left hy,
      abs_of_nonneg (by linarith : 0 ≤ x - -1), abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · by_cases hy' : 1 ≤ y
    · rw [unitTestClip, min_eq_left hy', max_eq_right (by norm_num : (-1 : ℝ) ≤ 1),
        abs_of_nonpos (by linarith : x - 1 ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
      linarith
    · rw [unitTestClip, min_eq_right (le_of_not_ge hy'), max_eq_right (le_of_not_ge hy)]

theorem exists_continuous_unit_test_l1 {X : Type*} [TopologicalSpace X] [NormalSpace X]
    [MeasurableSpace X] [BorelSpace X] [R1Space X] [WeaklyLocallyCompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (f : X → ℝ)
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, Continuous g ∧ HasCompactSupport g ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      Integrable g μ ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  obtain ⟨u, hus, herr, huc, hui⟩ := hfi.exists_hasCompactSupport_integral_sub_le hε
  let g := fun x => unitTestClip (u x)
  have hgc : Continuous g := unitTestClip_continuous.comp huc
  have hgb : ∀ x, ‖g x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_le]
    exact unitTestClip_mem (u x)
  have hgi : Integrable g μ := (integrable_const (1 : ℝ)).mono' hgc.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)
  refine ⟨g, hgc, hus.comp_left unitTestClip_zero, hgb, hgi, ?_⟩
  apply (integral_mono (hfi.sub hgi).norm (hfi.sub hui).norm ?_).trans herr
  intro x
  exact unitTestClip_error (by simpa only [Real.norm_eq_abs] using hbound x) (u x)

end Erdos3

end

end OAI
