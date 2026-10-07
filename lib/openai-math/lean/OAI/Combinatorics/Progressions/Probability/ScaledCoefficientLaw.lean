import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem affineProbabilityProfile_scaled_support {c w S x : ℝ} (hw : 0 < w) (hS : 0 < S)
    (hx : affineProbabilityProfile (c / S) (w / S) x ≠ 0) :
    |x * S - c| < 3 * w / 4 := by
  have hb := mul_lt_mul_of_pos_right
    (affineProbabilityProfile_support (c / S) (div_pos hw hS) hx) hS
  have hl : |x - c / S| * S = |x * S - c| := by
    calc
      _ = |(x - c / S) * S| := by rw [abs_mul, abs_of_pos hS]
      _ = _ := by rw [sub_mul, div_mul_cancel₀ _ hS.ne']
  have hr : 3 * (w / S) / 4 * S = 3 * w / 4 := by field_simp
  rwa [hl, hr] at hb

noncomputable def scaledCoefficientDensity {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (c w : J → ℝ) : (J → ℝ) → ℝ :=
  affineProductProfile (fun j => c j / monomialScale T (e j))
    (fun j => w j / monomialScale T (e j))

theorem scaledCoefficientDensity_measurable {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (c w : J → ℝ) :
    Measurable (scaledCoefficientDensity e T c w) :=
  (affineProductProfile_contDiff _ _).continuous.measurable

theorem scaledCoefficientDensity_nonneg {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) (a : J → ℝ) : 0 ≤ scaledCoefficientDensity e T c w a :=
  affineProductProfile_nonneg _ _ (fun j => div_pos (hw j) (monomialScale_pos T hT (e j))) a

theorem scaledCoefficientDensity_integrable {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) : Integrable (scaledCoefficientDensity e T c w) :=
  affineProductProfile_integrable _ _ (fun j => div_pos (hw j) (monomialScale_pos T hT (e j)))

theorem scaledCoefficientDensity_integral {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) : (∫ a, scaledCoefficientDensity e T c w a) = 1 :=
  affineProductProfile_integral _ _ (fun j => div_pos (hw j) (monomialScale_pos T hT (e j)))

theorem scaledCoefficientDensity_probability {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) :
    IsProbabilityMeasure (realDensityMeasure volume (scaledCoefficientDensity e T c w)) :=
  realDensityMeasure_probability volume _ (scaledCoefficientDensity_integrable e T hT c w hw)
    (scaledCoefficientDensity_nonneg e T hT c w hw) (scaledCoefficientDensity_integral e T hT c w hw)

theorem scaledCoefficientDensity_law {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) :
    (realDensityMeasure volume (smoothProductProfile J)).map
      (fun r j => (c j + w j * r j) / monomialScale T (e j)) =
      realDensityMeasure volume (scaledCoefficientDensity e T c w) := by
  have heq : (fun (r : J → ℝ) j => (c j + w j * r j) / monomialScale T (e j)) =
      (fun (r : J → ℝ) j => c j / monomialScale T (e j) + (w j / monomialScale T (e j)) * r j) := by
    funext r j
    ring
  rw [heq]
  exact affineProductProfile_law _ _ (fun j => div_pos (hw j) (monomialScale_pos T hT (e j)))

theorem scaledCoefficientDensity_support {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) {a : J → ℝ} (ha : scaledCoefficientDensity e T c w a ≠ 0) (j : J) :
    |a j * monomialScale T (e j) - c j| < 3 * w j / 4 := by
  classical
  apply affineProbabilityProfile_scaled_support (hw j) (monomialScale_pos T hT (e j))
  exact (Finset.prod_ne_zero_iff.mp ha) j (Finset.mem_univ j)

theorem scaledCoefficientDensity_coefficient_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) {a : J → ℝ} (ha : scaledCoefficientDensity e T c w a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ |c j| + w j := by
  have hb := scaledCoefficientDensity_support e T hT c w hw ha j
  have ht := abs_add_le (a j * monomialScale T (e j) - c j) (c j)
  rw [sub_add_cancel, abs_mul, abs_of_pos (monomialScale_pos T hT (e j))] at ht
  linarith [hw j]

theorem scaledCoefficientDensity_box_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (c w : J → ℝ)
    (hw : ∀ j, 0 < w j) {a : J → ℝ} (ha : scaledCoefficientDensity e T c w a ≠ 0)
    (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ ∑ j, (|c j| + w j) :=
  monomialArrayPolynomial_box_budget e a _ T x hx
    (scaledCoefficientDensity_coefficient_bound e T hT c w hw ha)

end Erdos3

end

end OAI
