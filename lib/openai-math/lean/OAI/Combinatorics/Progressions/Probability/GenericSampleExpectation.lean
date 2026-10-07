import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {Ω Z V Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSpace V] [MeasurableSpace Y]

theorem genericSampleDoubleExpectation_measurable
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (f : Ω × V → Y) (hf : Measurable f)
    (φ : Ω × (Z × Y) → ℂ) (hφ : Measurable φ) :
    Measurable (fun s => ∫ z, ∫ x, φ (s, (z, f (s, x))) ∂ν ∂μ) := by
  have hs : Measurable (fun p : (Ω × Z) × V => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hz : Measurable (fun p : (Ω × Z) × V => p.1.2) :=
    measurable_snd.comp measurable_fst
  have hj : Measurable (fun p : (Ω × Z) × V =>
      φ (p.1.1, (p.1.2, f (p.1.1, p.2)))) :=
    hφ.comp (hs.prodMk (hz.prodMk (hf.comp (hs.prodMk measurable_snd))))
  have hi : Measurable (fun p : Ω × Z => ∫ x, φ (p.1, (p.2, f (p.1, x))) ∂ν) :=
    hj.stronglyMeasurable.integral_prod_right'.measurable
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
theorem genericSampleDoubleExpectation_norm_le
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (f : Ω × V → Y) (φ : Ω × (Z × Y) → ℂ)
    (hφ : ∀ p, ‖φ p‖ ≤ 1) (s : Ω) :
    ‖∫ z, ∫ x, φ (s, (z, f (s, x))) ∂ν ∂μ‖ ≤ 1 := by
  have hi (z : Z) : ‖∫ x, φ (s, (z, f (s, x))) ∂ν‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := ν)
      (Filter.Eventually.of_forall (fun x => hφ (s, (z, f (s, x)))))
  simpa using norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall hi)

theorem genericSampleFiniteExpectation_measurable
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {T : Type*} [Fintype T] (p : FiniteProbabilityWeights T) (input : T → V)
    (f : Ω × V → Y) (hf : Measurable f)
    (φ : Ω × (Z × Y) → ℂ) (hφ : Measurable φ) :
    Measurable (fun s => ∫ z, p.complexMean
      (fun t => φ (s, (z, f (s, input t)))) ∂μ) := by
  have hj (t : T) : Measurable (fun q : Ω × Z =>
      φ (q.1, (q.2, f (q.1, input t)))) :=
    hφ.comp (measurable_fst.prodMk (measurable_snd.prodMk
      (hf.comp (measurable_fst.prodMk measurable_const))))
  have hi : Measurable (fun q : Ω × Z =>
      p.complexMean (fun t => φ (q.1, (q.2, f (q.1, input t))))) :=
    p.complexMean_measurable _ hj
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSpace Y] in
theorem genericSampleFiniteExpectation_norm_le
    (μ : Measure Z) [IsProbabilityMeasure μ]
    {T : Type*} [Fintype T] (p : FiniteProbabilityWeights T) (input : T → V)
    (f : Ω × V → Y) (φ : Ω × (Z × Y) → ℂ)
    (hφ : ∀ q, ‖φ q‖ ≤ 1) (s : Ω) :
    ‖∫ z, p.complexMean (fun t => φ (s, (z, f (s, input t)))) ∂μ‖ ≤ 1 := by
  have hi (z : Z) : ‖p.complexMean (fun t => φ (s, (z, f (s, input t))))‖ ≤ 1 :=
    (p.norm_complexMean_le_mean_norm _).trans
      ((p.mean_mono (fun t => hφ (s, (z, f (s, input t))))).trans_eq (p.mean_const 1))
  simpa using norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall hi)

end Erdos3

end

end OAI
