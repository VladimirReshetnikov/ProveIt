import OAI.Combinatorics.Progressions.Sampling.ControlledJointGrid

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators

theorem density_complex_test_lipschitz {X : Type*} [PseudoMetricSpace X]
    (g : X → ℝ) (φ : X → ℂ) (C L K : ℝ≥0)
    (hg : LipschitzWith L g) (hφ : LipschitzWith K φ)
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    LipschitzWith (L + C * K) (fun x => (g x : ℂ) * φ x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have hg' : ‖(g x : ℂ) - g y‖ ≤ (L : ℝ) * dist x y := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, ← dist_eq_norm] using hg.dist_le_mul x y
  have hφ' : ‖φ x - φ y‖ ≤ (K : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hφ.dist_le_mul x y
  calc
    _ = ‖((g x : ℂ) - g y) * φ x + (g y : ℂ) * (φ x - φ y)‖ := by congr 1; ring
    _ ≤ ‖((g x : ℂ) - g y) * φ x‖ + ‖(g y : ℂ) * (φ x - φ y)‖ := norm_add_le _ _
    _ ≤ ((L : ℝ) * dist x y) * 1 + C * ((K : ℝ) * dist x y) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hg' (hbound x) (norm_nonneg _) (by positivity))
        (mul_le_mul (hcap y) hφ' (norm_nonneg _) C.coe_nonneg)
    _ = _ := by push_cast; ring

theorem scaledRectangular_density_complex_test_quadrature {J : Type*} [Fintype J]
    (g : (J → ℝ) → ℝ) (φ : (J → ℝ) → ℂ) (C L K : ℝ≥0)
    (hg : LipschitzWith L g) (hφ : LipschitzWith K φ)
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (c T : J → ℝ) {q : ℝ} (hq : 0 < q)
    (hT : ∀ j, 0 < T j) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hmesh : ∀ j, q / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖((q ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
        (∑' z : J → ℤ,
          (g (fun j => (c j + q * z j) / T j) : ℂ) *
            φ (fun j => (c j + q * z j) / T j)) -
        ∫ x, φ x ∂realDensityMeasure volume g‖ ≤
      2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ := by
  rw [realDensityMeasure_integral_complex volume g hg.continuous.measurable hg0]
  simpa only [NNReal.coe_add, NNReal.coe_mul] using
    scaledRectangular_complex_quadrature (fun x => (g x : ℂ) * φ x)
      (density_complex_test_lipschitz g φ C L K hg hφ hcap hbound)
      c T hq hT hR hδ hδ1 hmesh
      (fun x hx => by rw [hsupport x hx, Complex.ofReal_zero, zero_mul])

end Erdos3

end

end OAI
