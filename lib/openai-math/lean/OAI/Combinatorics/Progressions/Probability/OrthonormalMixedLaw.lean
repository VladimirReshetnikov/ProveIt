import OAI.Combinatorics.Progressions.Estimates.MixedCoefficientCounting
import OAI.Combinatorics.Progressions.Lattices.EuclideanShortLatticeBasis

namespace OAI

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I] [Fintype J]

noncomputable def orthonormalMixedChart (b : OrthonormalBasis I ℝ E) :
    ((I → ℝ) × (J → ℤ)) ≃ᵐ (E × (J → ℤ)) :=
  (orthonormalChart b).toHomeomorph.toMeasurableEquiv.prodCongr (MeasurableEquiv.refl _)

theorem orthonormalMixedChart_measurePreserving (b : OrthonormalBasis I ℝ E) :
    MeasurePreserving (orthonormalMixedChart (J := J) b)
      ((volume : Measure (I → ℝ)).prod Measure.count) (volume.prod Measure.count) :=
  (orthonormalChart_measurePreserving b).prod (MeasurePreserving.id Measure.count)

noncomputable def orthonormalMixedDensity (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (p : J → PMF ℤ) (x : E × (J → ℤ)) : ℝ :=
  mixedCoefficientDensity c w p ((orthonormalMixedChart b).symm x)

omit [FiniteDimensional ℝ E] in
theorem orthonormalMixedDensity_measurable (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (p : J → PMF ℤ) : Measurable (orthonormalMixedDensity b c w p) := by
  have hf : Measurable (mixedCoefficientDensity c w p) :=
    binaryDensity_measurable (affineProductProfile_contDiff c w).continuous.measurable
      (measurable_of_countable (fun z : J → ℤ => ∏ j, (p j (z j)).toReal))
  exact hf.comp (orthonormalMixedChart b).symm.measurable

omit [FiniteDimensional ℝ E] in
theorem orthonormalMixedDensity_nonneg (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) (x) :
    0 ≤ orthonormalMixedDensity b c w p x := mixedCoefficientDensity_nonneg c w hw p _

theorem orthonormalMixedDensity_law (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    Measure.map (orthonormalMixedChart b) (mixedCoefficientLaw c w p) =
      realDensityMeasure (volume.prod Measure.count) (orthonormalMixedDensity b c w p) := by
  rw [mixedCoefficientLaw_count_density c w hw p,
    realDensityMeasure_map_equiv (orthonormalMixedChart b),
    (orthonormalMixedChart_measurePreserving b).map_eq]
  rfl

end Erdos3

end

end OAI
