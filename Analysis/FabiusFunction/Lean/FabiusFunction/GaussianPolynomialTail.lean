import FabiusFunction.GaussianPolynomialContraction
import FabiusFunction.FabiusSaddleReferenceTail

/-!
# Explicit tails for Gaussian-weighted complex polynomials

An arbitrary-order saddle reference is a standard Gaussian multiplied by a
finite complex polynomial.  This module bounds its complementary-interval
integral coefficient by coefficient.  Combined with an order-dependent
central radius, the estimate makes every fixed polynomial reference smaller
than any requested inverse power of the saddle scale.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace Fabius.SaddleExpansion

/-- A finite factorial coefficient weight controlling both the tail and the
whole-line `L¹` norm of a Gaussian-weighted complex polynomial. -/
noncomputable def gaussianPolynomialTailWeight (p : Polynomial ℂ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖ * (8 * k.factorial)

/-- The factorial coefficient weight is nonnegative. -/
lemma gaussianPolynomialTailWeight_nonneg (p : Polynomial ℂ) :
    0 ≤ gaussianPolynomialTailWeight p := by
  unfold gaussianPolynomialTailWeight
  positivity

/-- Exact coefficientwise tail estimate for a Gaussian-weighted complex
polynomial outside `[-A,A]`. -/
theorem integral_norm_standardGaussian_mul_eval_compl_Icc_le
    (p : Polynomial ℂ) {A : ℝ} (hA : 4 ≤ A) :
    (∫ v in (Icc (-A) A)ᶜ,
      ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) ≤
        ∑ k ∈ p.support,
          ‖p.coeff k‖ *
            (8 * k.factorial * Real.exp (-(A ^ 2) / 4) / A) := by
  let g : ℕ → ℝ → ℝ := fun k v =>
    ‖p.coeff k‖ * (Real.exp (-(v ^ 2) / 2) * |v| ^ k)
  have hg (k : ℕ) : Integrable (g k) :=
    (integrable_realGaussian_mul_abs_pow k).const_mul _
  have hleft : Integrable (fun v : ℝ =>
      ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) :=
    (integrable_standardGaussian_mul_eval p).norm
  have hmajor : Integrable
      (fun v : ℝ => ∑ k ∈ p.support, g k v) := by
    exact integrable_finsetSum p.support (fun k _ => hg k)
  have hpoint (v : ℝ) :
      ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖ ≤
        ∑ k ∈ p.support, g k v := by
    simpa only [g] using norm_standardGaussian_mul_eval_le p v
  have hmono :
      (∫ v in (Icc (-A) A)ᶜ,
        ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) ≤
      ∫ v in (Icc (-A) A)ᶜ, ∑ k ∈ p.support, g k v := by
    exact setIntegral_mono_on hleft.integrableOn hmajor.integrableOn
      measurableSet_Icc.compl (fun v _ => hpoint v)
  calc
    (∫ v in (Icc (-A) A)ᶜ,
        ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) ≤
      ∫ v in (Icc (-A) A)ᶜ, ∑ k ∈ p.support, g k v := hmono
    _ = ∑ k ∈ p.support,
        ‖p.coeff k‖ *
          (∫ v in (Icc (-A) A)ᶜ,
            Real.exp (-(v ^ 2) / 2) * |v| ^ k) := by
      rw [integral_finsetSum p.support]
      · apply Finset.sum_congr rfl
        intro k _hk
        rw [integral_const_mul]
      · intro k _hk
        exact (hg k).integrableOn
    _ ≤ ∑ k ∈ p.support,
        ‖p.coeff k‖ *
          (8 * k.factorial * Real.exp (-(A ^ 2) / 4) / A) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact mul_le_mul_of_nonneg_left
        (Fabius.SaddleCentral.integral_gaussian_abs_pow_compl_Icc_le k hA)
        (norm_nonneg _)

/-- Tail estimate expressed through the common factorial coefficient weight. -/
theorem integral_norm_standardGaussian_mul_eval_compl_Icc_le_tailWeight
    (p : Polynomial ℂ) {A : ℝ} (hA : 4 ≤ A) :
    (∫ v in (Icc (-A) A)ᶜ,
      ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) ≤
        gaussianPolynomialTailWeight p *
          (Real.exp (-(A ^ 2) / 4) / A) := by
  calc
    (∫ v in (Icc (-A) A)ᶜ,
        ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) ≤
      ∑ k ∈ p.support,
        ‖p.coeff k‖ *
          (8 * k.factorial * Real.exp (-(A ^ 2) / 4) / A) :=
      integral_norm_standardGaussian_mul_eval_compl_Icc_le p hA
    _ = gaussianPolynomialTailWeight p *
        (Real.exp (-(A ^ 2) / 4) / A) := by
      unfold gaussianPolynomialTailWeight
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      ring

end Fabius.SaddleExpansion
