import OAI.Combinatorics.Progressions.Geometry.BoxTestSmoothing

namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def mappedTest {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Ω → X) (φ : X → ℝ) : ℝ := ∫ a, φ (U a) ∂μ

theorem mappedTest_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → X) (hU : Measurable U)
    (φ : X → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    Integrable (fun a => φ (U a)) μ :=
  (integrable_const (1 : ℝ)).mono' (hφ.comp hU).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a => hbound (U a)))

theorem mappedTest_norm_le {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → X) (φ : X → ℝ)
    (hbound : ∀ x, ‖φ x‖ ≤ 1) : ‖mappedTest μ U φ‖ ≤ μ.real Set.univ := by
  have h := norm_integral_le_of_norm_le (integrable_const (1 : ℝ) (μ := μ))
    (Filter.Eventually.of_forall (fun a => hbound (U a)))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  exact h

theorem mappedTest_shift_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [SFinite μ] (U : Ω → (ι → ℝ)) (hU : Measurable U)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) :
    Measurable (fun z => mappedTest μ U (fun x => φ (x + z))) := by
  have hm : Measurable (fun p : Ω × (ι → ℝ) => φ (U p.1 + p.2)) :=
    hφ.comp ((hU.comp measurable_fst).add measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem coupled_mappedTest_difference {Ω X : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hmass : μ.real Set.univ ≤ 1)
    (U V : Ω → X) (hU : Measurable U) (hV : Measurable V)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ᵐ a ∂μ, dist (U a) (V a) ≤ ε)
    (φ : X → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L φ) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤ L * ε := by
  have hiU := mappedTest_integrable μ U hU φ hφ hbound
  have hiV := mappedTest_integrable μ V hV φ hφ hbound
  have hp : ∀ᵐ a ∂μ, ‖φ (U a) - φ (V a)‖ ≤ (L : ℝ) * ε := by
    filter_upwards [hclose] with a ha
    have h := (hL.dist_le_mul (U a) (V a)).trans (mul_le_mul_of_nonneg_left ha L.coe_nonneg)
    simpa only [Real.dist_eq, Real.norm_eq_abs] using h
  have h := norm_integral_le_of_norm_le (integrable_const ((L : ℝ) * ε) (μ := μ)) hp
  rw [integral_sub hiU hiV, Real.norm_eq_abs, integral_const, smul_eq_mul] at h
  exact h.trans (by nlinarith [mul_nonneg L.coe_nonneg hε])

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

theorem mappedTest_box_average (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U) (δ : ℝ)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    mappedTest μ U (boxTestAverage δ φ) =
      ∫ u, boxProbabilityWindow (fun _ => δ) 0 u * mappedTest μ U (fun x => φ (x + u)) := by
  have hi : Integrable (Function.uncurry
      (fun a u => boxProbabilityWindow (fun _ => δ) 0 u * φ (U a + u))) (μ.prod volume) :=
    ((boxProbabilityWindow_integrable (fun _ => δ) 0).comp_snd μ).mul_bdd
      (hφ.comp ((hU.comp measurable_fst).add measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound (U p.1 + p.2)))
  calc
    mappedTest μ U (boxTestAverage δ φ) =
        ∫ a, ∫ u, boxProbabilityWindow (fun _ => δ) 0 u * φ (U a + u) ∂volume ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with a
      exact boxTestAverage_translate δ φ (U a)
    _ = ∫ u, ∫ a, boxProbabilityWindow (fun _ => δ) 0 u * φ (U a + u) ∂μ :=
      integral_integral_swap hi
    _ = ∫ u, boxProbabilityWindow (fun _ => δ) 0 u * mappedTest μ U (fun x => φ (x + u)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact integral_const_mul _ _

theorem mappedTest_box_error (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U) (δ : ℝ) (hδ : 0 < δ) (H : ℝ≥0)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (hmove : ∀ z, |mappedTest μ U (fun x => φ (x + z)) - mappedTest μ U φ| ≤ H * dist z 0) :
    |mappedTest μ U (boxTestAverage δ φ) - mappedTest μ U φ| ≤ H * δ := by
  let k := boxProbabilityWindow (fun _ : ι => δ) 0
  let A := fun z => mappedTest μ U (fun x => φ (x + z))
  let I := mappedTest μ U φ
  have hk : Integrable k := boxProbabilityWindow_integrable _ _
  have ha : Integrable (fun u => k u * A u) := hk.mul_bdd
    (mappedTest_shift_measurable μ U hU φ hφ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => mappedTest_norm_le μ U (fun x => φ (x + z))
      (fun x => hbound (x + z))))
  have hconst : (∫ u, k u * I) = I := by
    rw [integral_mul_const, boxProbabilityWindow_mass _ (fun _ => hδ), one_mul]
  have heq : mappedTest μ U (boxTestAverage δ φ) - I = ∫ u, k u * A u - k u * I := by
    rw [integral_sub ha (hk.mul_const I), hconst]
    rw [mappedTest_box_average μ U hU δ φ hφ hbound]
  have hpoint (u : ι → ℝ) : ‖k u * A u - k u * I‖ ≤ k u * ((H : ℝ) * δ) := by
    by_cases hzero : k u = 0
    · simp only [hzero, zero_mul, sub_self, norm_zero, le_refl]
    · have hdist := boxProbabilityWindow_support_dist δ hδ u hzero
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (boxProbabilityWindow_nonneg _ (fun _ => hδ) _ _),
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((hmove u).trans (mul_le_mul_of_nonneg_left hdist H.coe_nonneg))
        (boxProbabilityWindow_nonneg _ (fun _ => hδ) _ _)
  have h := norm_integral_le_of_norm_le (hk.mul_const ((H : ℝ) * δ)) (Filter.Eventually.of_forall hpoint)
  rw [integral_mul_const, boxProbabilityWindow_mass _ (fun _ => hδ), one_mul, Real.norm_eq_abs] at h
  rw [heq]
  exact h

end Erdos3

end

end OAI
