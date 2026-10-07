import OAI.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem haarShiftDensity_map_eq {T G Y : Type*} [MeasurableSpace T] [AddCommGroup G]
    [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G] [MeasurableSpace Y]
    (μ : Measure G) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] (z : T → G) (hz : Measurable z)
    (f : G → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1)
    (π : G → Y) (hπ : Measurable π) (hinv : ∀ t x, π (x + z t) = π x) :
    (realDensityMeasure μ (haarShiftDensity ν z f)).map π = (realDensityMeasure μ f).map π := by
  let _ := realDensityMeasure_probability μ f hfi hf0 hmass
  have hU : Measurable (fun p : T × G => p.2 + z p.1) :=
    measurable_snd.add (hz.comp measurable_fst)
  rw [← haarShiftDensity_image_law μ ν hz hfm hfi hf0 hmass,
    Measure.map_map hπ hU]
  have he : (π ∘ fun p : T × G => p.2 + z p.1) = π ∘ Prod.snd := by
    funext p
    exact hinv p.1 p.2
  rw [he, ← Measure.map_map hπ measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

end Erdos3

end

end OAI
