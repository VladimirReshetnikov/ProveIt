import OAI.Combinatorics.Progressions.Probability.MixedDensityInterpolation

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

variable {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
variable (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)

noncomputable def integerMatrixRealDensity (f : (J → ℝ) → ℝ) : (O → ℝ) → ℝ :=
  selectedCoefficientDensity A s hA (fun _ => 1) (fun _ => 1)
    (fun _ => zero_lt_one) (fun _ => zero_lt_one) f

theorem integerMatrixRealDensity_measurable {f : (J → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (integerMatrixRealDensity A s hA f) :=
  pivotOutputDensity_measurable _ _
    (hf.comp (selectedCoefficientMeasurableEquiv s).measurable)

theorem integerMatrixRealDensity_nonneg {f : (J → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (x : O → ℝ) : 0 ≤ integerMatrixRealDensity A s hA f x :=
  pivotOutputDensity_nonneg _ _ (selectedCoefficientProfile_nonneg s hf) x

theorem integerMatrixRealDensity_integrable {f : (J → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (integerMatrixRealDensity A s hA f) :=
  pivotOutputDensity_integrable _ _ (selectedCoefficientProfile_integrable s hf)

theorem integerMatrixRealDensity_integral {f : (J → ℝ) → ℝ} (hf : Integrable f) :
    (∫ x, integerMatrixRealDensity A s hA f x) = ∫ x, f x :=
  (pivotOutputDensity_integral _ _ (selectedCoefficientProfile_integrable s hf)).trans
    (selectedCoefficientProfile_integral s f)

theorem integerMatrixRealDensity_law {f : (J → ℝ) → ℝ}
    (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) :
    (realDensityMeasure volume f).map (fun x => A.map (Int.cast : ℤ → ℝ) *ᵥ x) =
      realDensityMeasure volume (integerMatrixRealDensity A s hA f) := by
  have h := selectedCoefficientDensity_law A s hA (fun _ => 1) (fun _ => 1)
    (fun _ => zero_lt_one) (fun _ => zero_lt_one) f hf hf0
  simpa only [normalizedIntegerColumns, inv_one, Matrix.diagonal_one,
    Matrix.one_mul, Matrix.mul_one, Int.coe_castRingHom, integerMatrixRealDensity] using h

omit [DecidableEq J] in
theorem affineCoefficientProduct_density (c w : J → ℝ) (hw : ∀ j, 0 < w j) :
    Measure.pi (fun j => affineCoefficientMeasure (c j) (w j)) =
      realDensityMeasure volume (affineProductProfile c w) :=
  independentCoordinateDensity_measure (fun j => affineProbabilityProfile (c j) (w j))
    (fun j => affineProbabilityProfile_integrable (c j) (hw j))
    (fun j => affineProbabilityProfile_nonneg (c j) (hw j))
    (fun j => affineProbabilityProfile_integral (c j) (hw j))

theorem integerMatrixRealDensity_affine_law (c w : J → ℝ) (hw : ∀ j, 0 < w j) :
    (Measure.pi (fun j => affineCoefficientMeasure (c j) (w j))).map
      (fun x => A.map (Int.cast : ℤ → ℝ) *ᵥ x) =
    realDensityMeasure volume (integerMatrixRealDensity A s hA (affineProductProfile c w)) := by
  rw [affineCoefficientProduct_density c w hw]
  exact integerMatrixRealDensity_law A s hA (affineProductProfile_integrable c w hw)
    (affineProductProfile_nonneg c w hw)

end Erdos3

end

end OAI
