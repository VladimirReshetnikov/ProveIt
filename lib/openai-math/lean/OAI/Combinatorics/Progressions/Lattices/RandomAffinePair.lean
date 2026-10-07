import OAI.Combinatorics.Progressions.Estimates.FourProductSmoothing

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem unitScalarMeasure_reflection (f : ℝ → ℝ) :
    (∫ u, f (1 - u) ∂unitScalarMeasure) = ∫ u, f u ∂unitScalarMeasure := by
  change (∫ u in Set.Ioc (0 : ℝ) 1, f (1 - u)) = ∫ u in Set.Ioc (0 : ℝ) 1, f u
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left f 1]
  norm_num

theorem uniform_signed_slope_normalize (a : ℝ) (f : ℝ → ℝ) :
    (∫ u, f (a * u) ∂unitScalarMeasure) =
      ∫ u, f (min 0 a + |a| * u) ∂unitScalarMeasure := by
  by_cases ha : 0 ≤ a
  · simp only [min_eq_left ha, abs_of_nonneg ha, zero_add]
  · have ha' : a < 0 := lt_of_not_ge ha
    calc
      (∫ u, f (a * u) ∂unitScalarMeasure) =
          ∫ u, f (a * (1 - u)) ∂unitScalarMeasure := (unitScalarMeasure_reflection _).symm
      _ = ∫ u, f (min 0 a + |a| * u) ∂unitScalarMeasure := by
        apply integral_congr_ae
        filter_upwards [] with u
        congr 1
        rw [min_eq_right ha'.le, abs_of_neg ha']
        ring

theorem uniform_two_affine_normalize (a b c : ℝ) (φ : ℝ → ℝ) :
    (∫ u, ∫ v, φ (c + a * u + b * v) ∂unitScalarMeasure ∂unitScalarMeasure) =
      ∫ u, ∫ v, φ (c + min 0 a + min 0 b + (|a| * u + |b| * v))
        ∂unitScalarMeasure ∂unitScalarMeasure := by
  have ha := uniform_signed_slope_normalize a
    (fun x => ∫ v, φ (c + x + b * v) ∂unitScalarMeasure)
  apply ha.trans
  apply integral_congr_ae
  filter_upwards [] with u
  have hb := uniform_signed_slope_normalize b (fun y => φ (c + (min 0 a + |a| * u) + y))
  apply hb.trans
  apply integral_congr_ae
  filter_upwards [] with v
  congr 1
  ring

theorem uniform_two_affine_sort (a b c : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ u, ∫ v, φ (c + min 0 a + min 0 b + min |a| |b| * u + max |a| |b| * v)
      ∂unitScalarMeasure ∂unitScalarMeasure) =
      ∫ u, ∫ v, φ (c + a * u + b * v) ∂unitScalarMeasure ∂unitScalarMeasure := by
  have h := uniform_two_term_sum_sort |a| |b|
    (fun z => φ (c + min 0 a + min 0 b + z))
    (hφ.comp (measurable_const.add measurable_id)) (fun z => hbound _)
  have hn := uniform_two_affine_normalize a b c φ
  simpa only [add_assoc] using h.trans hn.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {T : Type*} [MeasurableSpace T]

noncomputable def affinePairWidth (a b : T → ℝ) (p : T × ℝ) : ℝ := max |a p.1| |b p.1|

noncomputable def affinePairShift (a b c : T → ℝ) (p : T × ℝ) : ℝ :=
  c p.1 + min 0 (a p.1) + min 0 (b p.1) + min |a p.1| |b p.1| * p.2

theorem affinePairWidth_measurable {a b : T → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (affinePairWidth a b) := (ha.abs.max hb.abs).comp measurable_fst

theorem affinePairShift_measurable {a b c : T → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (affinePairShift a b c) := by
  unfold affinePairShift
  fun_prop

noncomputable def affinePairDensity (μ : Measure T) (a b c : T → ℝ) : ℝ → ℝ :=
  randomIntervalDensity (μ.prod unitScalarMeasure) (affinePairWidth a b) (affinePairShift a b c)

theorem affinePairDensity_measurable (μ : Measure T) [SFinite μ] {a b c : T → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (affinePairDensity μ a b c) :=
  randomIntervalDensity_measurable _ _ _ (affinePairWidth_measurable ha hb)
    (affinePairShift_measurable ha hb hc)

theorem affinePairWidth_inverse_integral (μ : Measure T) [SFinite μ] (a b : T → ℝ) :
    (∫ p, (affinePairWidth a b p)⁻¹ ∂μ.prod unitScalarMeasure) =
      ∫ t, (max |a t| |b t|)⁻¹ ∂μ := by
  unfold affinePairWidth
  rw [integral_fun_fst (fun t => (max |a t| |b t|)⁻¹), probReal_univ, one_smul]

theorem affinePairDensity_cap (μ : Measure T) [IsProbabilityMeasure μ] {a b c : T → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hpos : ∀ᵐ t ∂μ, 0 < max |a t| |b t|)
    (hi : Integrable (fun t => (max |a t| |b t|)⁻¹) μ) (x : ℝ) :
    affinePairDensity μ a b c x ∈ Set.Icc (0 : ℝ) (∫ t, (max |a t| |b t|)⁻¹ ∂μ) := by
  have h := randomIntervalDensity_cap (μ.prod unitScalarMeasure) _ _
    (affinePairWidth_measurable ha hb) (affinePairShift_measurable ha hb hc)
    (Measure.quasiMeasurePreserving_fst.ae hpos) (hi.comp_fst unitScalarMeasure) x
  rw [affinePairWidth_inverse_integral] at h
  exact h

theorem affinePairDensity_probability_density (μ : Measure T) [IsProbabilityMeasure μ]
    {a b c : T → ℝ} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hpos : ∀ᵐ t ∂μ, 0 < max |a t| |b t|) :
    (∀ x, 0 ≤ affinePairDensity μ a b c x) ∧ Integrable (affinePairDensity μ a b c) ∧
      (∫ x, affinePairDensity μ a b c x) = 1 :=
  randomIntervalDensity_probability_density _ _ _ (affinePairWidth_measurable ha hb)
    (affinePairShift_measurable ha hb hc) (Measure.quasiMeasurePreserving_fst.ae hpos)

theorem affinePairDensity_translation_l1 (μ : Measure T) [IsProbabilityMeasure μ]
    {a b c : T → ℝ} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hpos : ∀ᵐ t ∂μ, 0 < max |a t| |b t|)
    (hi : Integrable (fun t => (max |a t| |b t|)⁻¹) μ) (x y : ℝ) :
    (∫ u, |affinePairDensity μ a b c (u + x) - affinePairDensity μ a b c (u + y)|) ≤
      2 * (∫ t, (max |a t| |b t|)⁻¹ ∂μ) * |x - y| := by
  have h := randomIntervalDensity_translation_l1 (μ.prod unitScalarMeasure) _ _
    (affinePairWidth_measurable ha hb) (affinePairShift_measurable ha hb hc)
    (Measure.quasiMeasurePreserving_fst.ae hpos) (hi.comp_fst unitScalarMeasure) x y
  rw [affinePairWidth_inverse_integral] at h
  exact h

theorem affinePairDensity_test_integral (μ : Measure T) [IsProbabilityMeasure μ]
    {a b c : T → ℝ} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hpos : ∀ᵐ t ∂μ, 0 < max |a t| |b t|) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, affinePairDensity μ a b c x * φ x) =
      ∫ t, ∫ u, ∫ v, φ (c t + a t * u + b t * v)
        ∂unitScalarMeasure ∂unitScalarMeasure ∂μ := by
  have h := randomIntervalDensity_test_integral (μ.prod unitScalarMeasure) _ _
    (affinePairWidth_measurable ha hb) (affinePairShift_measurable ha hb hc)
    (Measure.quasiMeasurePreserving_fst.ae hpos) φ hφ hbound
  apply h.trans
  have hm : Measurable (fun p : (T × ℝ) × ℝ =>
      φ (affinePairShift a b c p.1 + affinePairWidth a b p.1 * p.2)) :=
    hφ.comp (((affinePairShift_measurable ha hb hc).comp measurable_fst).add
      (((affinePairWidth_measurable ha hb).comp measurable_fst).mul measurable_snd))
  have hi : Integrable (fun p : (T × ℝ) × ℝ =>
      φ (affinePairShift a b c p.1 + affinePairWidth a b p.1 * p.2))
      ((μ.prod unitScalarMeasure).prod unitScalarMeasure) :=
    (integrable_const C).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound _))
  rw [integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with t
  exact uniform_two_affine_sort (a t) (b t) (c t) φ hφ hbound

end Erdos3

end

end OAI
