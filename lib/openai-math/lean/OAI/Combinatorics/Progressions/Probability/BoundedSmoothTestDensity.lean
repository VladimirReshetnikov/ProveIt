import OAI.Combinatorics.Progressions.Estimates.CompactSmoothApproximation
import OAI.Combinatorics.Progressions.Estimates.UnitTestClipping

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_unit_uniform_approx (f : E → ℝ) (hf : Continuous f)
    (hs : HasCompactSupport f) (hbound : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      ∀ x, ‖g x - f x‖ ≤ 2 * δ := by
  obtain ⟨u, hu, hus, herr⟩ := exists_compact_smooth_uniform_approx f hf hs hδ
  have hd : 0 < 1 + δ := by linarith
  have hub (x : E) : ‖u x‖ ≤ 1 + δ := by
    calc
      ‖u x‖ = ‖(u x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖u x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ 1 + δ := by linarith [herr x, hbound x]
  have hgb (x : E) : ‖u x / (1 + δ)‖ ≤ 1 := by
    rw [norm_div, Real.norm_of_nonneg hd.le]
    exact (div_le_one hd).mpr (hub x)
  refine ⟨fun x => u x / (1 + δ), hu.div_const _,
    hus.comp_left (g := fun y : ℝ => y / (1 + δ)) (zero_div _), hgb, ?_⟩
  intro x
  have hid : u x / (1 + δ) - u x = -δ * (u x / (1 + δ)) := by
    field_simp
    ring
  calc
    ‖u x / (1 + δ) - f x‖ ≤ ‖u x / (1 + δ) - u x‖ + ‖u x - f x‖ := by
      simpa only [dist_eq_norm] using dist_triangle (u x / (1 + δ)) (u x) (f x)
    _ = δ * ‖u x / (1 + δ)‖ + ‖u x - f x‖ := by
      rw [hid, norm_mul, norm_neg, Real.norm_of_nonneg hδ.le]
    _ ≤ 2 * δ := by nlinarith [hgb x, herr x]

theorem exists_smooth_unit_test_l1 [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] [μ.Regular] (f : E → ℝ)
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      Integrable g μ ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  obtain ⟨v, hvc, hvs, hvb, hvi, herr⟩ := exists_continuous_unit_test_l1 μ f hf hbound (half_pos hε)
  let m := μ.real Set.univ
  have hm : 0 ≤ m := measureReal_nonneg
  let δ := ε / (4 * (m + 1))
  have hd : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hgc, hgs, hgb, hgv⟩ := exists_smooth_unit_uniform_approx v hvc hvs hvb hd
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have hgi : Integrable g μ := (integrable_const (1 : ℝ)).mono' hgc.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)
  refine ⟨g, hgc, hgs, hgb, hgi, ?_⟩
  have hpoint (x : E) : ‖f x - g x‖ ≤ ‖f x - v x‖ + 2 * δ := by
    have h : ‖f x - g x‖ ≤ ‖f x - v x‖ + ‖v x - g x‖ := by
      simpa only [dist_eq_norm] using dist_triangle (f x) (v x) (g x)
    rw [norm_sub_rev (v x) (g x)] at h
    linarith [hgv x]
  have hi : Integrable (fun x => ‖f x - v x‖ + 2 * δ) μ :=
    (hfi.sub hvi).norm.add (integrable_const _)
  have hfv : Integrable (fun x => ‖f x - v x‖) μ := (hfi.sub hvi).norm
  have h := integral_mono (hfi.sub hgi).norm hi hpoint
  rw [integral_add hfv (integrable_const _), integral_const, smul_eq_mul] at h
  have hδeq : 4 * (m + 1) * δ = ε := by
    dsimp only [δ]
    field_simp
  have hcost : m * (2 * δ) ≤ ε / 2 := by nlinarith
  change (∫ x, ‖f x - g x‖ ∂μ) ≤ (∫ x, ‖f x - v x‖ ∂μ) + m * (2 * δ) at h
  linarith

end Erdos3

end

end OAI
