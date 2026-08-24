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

private theorem norm_standardGaussian (v : ℝ) :
    ‖QuantitativeSaddle.standardGaussian v‖ =
      Real.exp (-(v ^ 2) / 2) := by
  rw [QuantitativeSaddle.standardGaussian, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

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
  have hg (k : ℕ) : Integrable (g k) := by
    have h := (integrable_realGaussian_mul_pow k).norm
    have habs : Integrable (fun v : ℝ =>
        Real.exp (-(v ^ 2) / 2) * |v| ^ k) := by
      apply h.congr
      filter_upwards with v
      rw [Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_pos (Real.exp_pos _)]
    exact habs.const_mul _
  have hleft : Integrable (fun v : ℝ =>
      ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) :=
    (integrable_standardGaussian_mul_eval p).norm
  have hmajor : Integrable
      (fun v : ℝ => ∑ k ∈ p.support, g k v) := by
    exact integrable_finsetSum p.support (fun k _ => hg k)
  have hpoint (v : ℝ) :
      ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖ ≤
        ∑ k ∈ p.support, g k v := by
    rw [norm_mul, norm_standardGaussian, Polynomial.eval_eq_sum]
    calc
      Real.exp (-(v ^ 2) / 2) *
          ‖p.sum fun k c => c * (v : ℂ) ^ k‖ ≤
        Real.exp (-(v ^ 2) / 2) *
          ∑ k ∈ p.support, ‖p.coeff k * (v : ℂ) ^ k‖ := by
            gcongr
            exact norm_sum_le _ _
      _ = ∑ k ∈ p.support, g k v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        simp only [norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs]
        dsimp [g]
        ring
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

end Fabius.SaddleExpansion
