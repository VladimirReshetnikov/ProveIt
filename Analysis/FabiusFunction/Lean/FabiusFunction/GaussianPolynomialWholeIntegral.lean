import FabiusFunction.GaussianPolynomialTailAllOrders

/-!
# Whole-line bounds for Gaussian-weighted polynomials

The arbitrary-order saddle expansion uses finite polynomial references.  This
module controls their full `L¹` norm by the same factorial coefficient weight
that controls their complementary tails.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics

namespace Fabius.SaddleExpansion

private lemma gaussian_abs_pow_le_integrable_majorant (k : ℕ) (v : ℝ) :
    Real.exp (-(v ^ 2) / 2) * |v| ^ k ≤
      k.factorial * Real.exp 1 * Real.exp (-(1 / 4 : ℝ) * |v|) := by
  have hu : 0 ≤ |v| := abs_nonneg v
  have hpow := Real.pow_div_factorial_le_exp |v| hu k
  have hk : (0 : ℝ) < k.factorial := by positivity
  have hpoly : |v| ^ k ≤ k.factorial * Real.exp |v| := by
    rw [div_le_iff₀ hk] at hpow
    simpa [mul_comm] using hpow
  have hv2 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
  have hexponent : -(v ^ 2) / 2 + |v| ≤ 1 - (1 / 4 : ℝ) * |v| := by
    rw [hv2]
    nlinarith [sq_nonneg (4 * |v| - 5)]
  calc
    Real.exp (-(v ^ 2) / 2) * |v| ^ k ≤
        Real.exp (-(v ^ 2) / 2) * (k.factorial * Real.exp |v|) := by
      gcongr
    _ = k.factorial * Real.exp (-(v ^ 2) / 2 + |v|) := by
      rw [Real.exp_add]
      ring_nf
    _ ≤ k.factorial * Real.exp (1 - (1 / 4 : ℝ) * |v|) := by
      gcongr
    _ = k.factorial * Real.exp 1 * Real.exp (-(1 / 4 : ℝ) * |v|) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring_nf

private lemma integral_exp_neg_quarter_abs :
    (∫ v : ℝ, Real.exp (-(1 / 4 : ℝ) * |v|)) = 8 := by
  have hi := Fabius.integrable_exp_neg_mul_abs
    (1 / 4 : ℝ) (by norm_num)
  have hsplit := integral_add_compl (s := Icc (-(0 : ℝ)) 0)
    measurableSet_Icc hi
  rw [show (∫ v in Icc (-(0 : ℝ)) 0,
      Real.exp (-(1 / 4 : ℝ) * |v|)) = 0 by simp] at hsplit
  have htail := Fabius.integral_exp_neg_mul_abs_compl_Icc
    (1 / 4 : ℝ) 0 (by norm_num) (by norm_num)
  rw [htail] at hsplit
  norm_num at hsplit
  simpa only [neg_mul] using hsplit.symm

/-- The whole Gaussian-weighted polynomial is controlled by its factorial
coefficient weight. -/
theorem integral_norm_standardGaussian_mul_eval_le
    (p : Polynomial ℂ) :
    (∫ v : ℝ, ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) ≤
      Real.exp 1 * gaussianPolynomialTailWeight p := by
  let g : ℕ → ℝ → ℝ := fun k v =>
    ‖p.coeff k‖ * (Real.exp (-(v ^ 2) / 2) * |v| ^ k)
  let major : ℕ → ℝ → ℝ := fun k v =>
    ‖p.coeff k‖ *
      (k.factorial * Real.exp 1 * Real.exp (-(1 / 4 : ℝ) * |v|))
  have hg (k : ℕ) : Integrable (g k) :=
    (integrable_realGaussian_mul_abs_pow k).const_mul _
  have hmajor (k : ℕ) : Integrable (major k) := by
    simpa only [major, mul_assoc] using
      (Fabius.integrable_exp_neg_mul_abs
        (1 / 4 : ℝ) (by norm_num)).const_mul
          (‖p.coeff k‖ * (k.factorial * Real.exp 1))
  have hleft : Integrable (fun v : ℝ =>
      ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) :=
    (integrable_standardGaussian_mul_eval p).norm
  have hsum : Integrable (fun v : ℝ => ∑ k ∈ p.support, major k v) :=
    integrable_finsetSum p.support (fun k _ => hmajor k)
  have hpoint (v : ℝ) :
      ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖ ≤
        ∑ k ∈ p.support, major k v := by
    calc
      ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖ ≤
          ∑ k ∈ p.support, g k v := by
        simpa only [g] using norm_standardGaussian_mul_eval_le p v
      _ ≤ ∑ k ∈ p.support, major k v := by
        apply Finset.sum_le_sum
        intro k _hk
        exact mul_le_mul_of_nonneg_left
          (gaussian_abs_pow_le_integrable_majorant k v) (norm_nonneg _)
  have hmono :
      (∫ v : ℝ, ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) ≤
        ∫ v : ℝ, ∑ k ∈ p.support, major k v := by
    exact integral_mono hleft hsum hpoint
  calc
    (∫ v : ℝ, ‖QuantitativeSaddle.standardGaussian v * p.eval (v : ℂ)‖) ≤
        ∫ v : ℝ, ∑ k ∈ p.support, major k v := hmono
    _ = ∑ k ∈ p.support,
        ‖p.coeff k‖ * (k.factorial * Real.exp 1 * 8) := by
      rw [integral_finsetSum p.support]
      · apply Finset.sum_congr rfl
        intro k _hk
        rw [integral_const_mul, integral_const_mul,
          integral_exp_neg_quarter_abs]
      · intro k _hk
        exact hmajor k
    _ = Real.exp 1 * gaussianPolynomialTailWeight p := by
      unfold gaussianPolynomialTailWeight
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring

/-- A family with bounded factorial coefficient weight has uniformly bounded
whole Gaussian-polynomial `L¹` norm. -/
theorem integral_norm_standardGaussian_mul_eval_isBigO_of_weight
    {α : Type*} (l : Filter α) (p : α → Polynomial ℂ)
    (hweight : (fun i => gaussianPolynomialTailWeight (p i)) =O[l]
      (fun _i => (1 : ℝ))) :
    (fun i => ∫ v : ℝ,
      ‖QuantitativeSaddle.standardGaussian v * (p i).eval (v : ℂ)‖)
        =O[l] (fun _i => (1 : ℝ)) := by
  apply (IsBigO.of_bound (Real.exp 1) ?_).trans hweight
  filter_upwards with i
  have hint : 0 ≤ (∫ v : ℝ,
      ‖QuantitativeSaddle.standardGaussian v * (p i).eval (v : ℂ)‖) :=
    integral_nonneg fun _ => norm_nonneg _
  have hw := gaussianPolynomialTailWeight_nonneg (p i)
  rw [Real.norm_eq_abs, abs_of_nonneg hint, Real.norm_eq_abs,
    abs_of_nonneg hw]
  exact integral_norm_standardGaussian_mul_eval_le (p i)

end Fabius.SaddleExpansion
