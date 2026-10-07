import OAI.Combinatorics.Progressions.Probability.MixedDensityInterpolation

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem integerCoordinate_count {J : Type*} [Fintype J] :
    Measure.pi (fun _ : J => (Measure.count : Measure ℤ)) = (Measure.count : Measure (J → ℤ)) := by
  apply Measure.ext_of_singleton
  intro z
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

theorem mixedCoefficientLaw_count_density {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    mixedCoefficientLaw c w p =
      realDensityMeasure ((volume : Measure (I → ℝ)).prod (Measure.count : Measure (J → ℤ)))
        (mixedCoefficientDensity c w p) := by
  simpa only [integerCoordinate_count] using mixedCoefficientLaw_density c w hw p

theorem mixedCoefficientDensity_count_integral {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    (∫ x, mixedCoefficientDensity c w p x
      ∂((volume : Measure (I → ℝ)).prod (Measure.count : Measure (J → ℤ)))) = 1 := by
  simpa only [integerCoordinate_count] using mixedCoefficientDensity_integral c w hw p

theorem mixedCoefficientDensity_sheet_integral {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : J → PMF ℤ) :
    (∑' z : J → ℤ, ∫ u : I → ℝ, mixedCoefficientDensity c w p (u, z)) = 1 := by
  have hi := mixedCoefficientDensity_integrable c w hw p
  rw [integerCoordinate_count] at hi
  have hm := mixedCoefficientDensity_count_integral c w hw p
  rw [integral_prod_symm _ hi, integral_countable hi.integral_prod_right] at hm
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul] using hm

end Erdos3

end

end OAI
