import FabiusFunction.GaussianPolynomialTail
import FabiusFunction.FabiusSaddleTailAllOrders

/-!
# Gaussian-polynomial tails at the all-orders saddle radius

This module upgrades the coefficientwise Gaussian-polynomial tail estimate to
the order-dependent radius used in the arbitrary-order Fabius saddle
expansion.  A phase-dependent polynomial family contributes a tail of order
`b⁻¹^(N+1)` whenever its finite coefficient weight remains bounded.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics

namespace Fabius.SaddleExpansion

private lemma exp_neg_sq_orderRadius_div_four
    (N : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    Real.exp (-(fabiusSaddleCentralRadiusOrder N b ^ 2) / 4) =
      b⁻¹ ^ (8 * (N + 1)) := by
  rw [sq_fabiusSaddleCentralRadiusOrder N hb]
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  rw [show -(32 * (N + 1 : ℝ) * Real.log b) / 4 =
      -((8 * (N + 1) : ℕ) * Real.log b) by push_cast; ring,
    Real.exp_neg, Real.exp_nat_mul, Real.exp_log hb0, inv_pow]

/-- A bounded family of complex polynomials has a Gaussian tail of arbitrary
algebraic order outside the corresponding saddle central radius. -/
theorem integral_norm_standardGaussian_mul_eval_orderRadius_isBigO
    {α : Type*} (l : Filter α) (N : ℕ)
    (b : α → ℝ) (p : α → Polynomial ℂ)
    (hb : Tendsto b l atTop)
    (hweight : (fun i => gaussianPolynomialTailWeight (p i)) =O[l]
      (fun _i => (1 : ℝ))) :
    (fun i => ∫ v in
      (Icc (-fabiusSaddleCentralRadiusOrder N (b i))
        (fabiusSaddleCentralRadiusOrder N (b i)))ᶜ,
      ‖QuantitativeSaddle.standardGaussian v * (p i).eval (v : ℂ)‖)
        =O[l] (fun i => (b i)⁻¹ ^ (N + 1)) := by
  let A : α → ℝ := fun i => fabiusSaddleCentralRadiusOrder N (b i)
  let w : α → ℝ := fun i => gaussianPolynomialTailWeight (p i)
  let rate : α → ℝ := fun i => (b i)⁻¹ ^ (N + 1)
  have hdom :
      (fun i => ∫ v in (Icc (-A i) (A i))ᶜ,
        ‖QuantitativeSaddle.standardGaussian v * (p i).eval (v : ℂ)‖)
        =O[l] (fun i => w i * rate i) := by
    apply IsBigO.of_bound 1
    filter_upwards [hb.eventually_ge_atTop (Real.exp 1)] with i hbi
    have hb1 : 1 ≤ b i :=
      (by have := Real.exp_one_gt_d9; linarith : (1 : ℝ) ≤ Real.exp 1).trans hbi
    have hb0 : 0 < b i := zero_lt_one.trans_le hb1
    have hlog : 1 ≤ Real.log (b i) :=
      (Real.le_log_iff_exp_le hb0).2 hbi
    have hA4 : 4 ≤ A i := by
      dsimp [A, fabiusSaddleCentralRadiusOrder]
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      nlinarith
    have hA1 : 1 ≤ A i := (by norm_num : (1 : ℝ) ≤ 4).trans hA4
    have htail :=
      integral_norm_standardGaussian_mul_eval_compl_Icc_le_tailWeight (p i) hA4
    have hexp := exp_neg_sq_orderRadius_div_four N hb1
    rw [hexp] at htail
    have hinv0 : 0 ≤ (b i)⁻¹ := by positivity
    have hinv1 : (b i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1
    have hpow : (b i)⁻¹ ^ (8 * (N + 1)) ≤ rate i := by
      dsimp [rate]
      exact pow_le_pow_of_le_one hinv0 hinv1 (by omega)
    have hAinv : (A i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA1
    have htail' :
        (∫ v in (Icc (-A i) (A i))ᶜ,
          ‖QuantitativeSaddle.standardGaussian v * (p i).eval (v : ℂ)‖) ≤
            w i * rate i := by
      calc
        (∫ v in (Icc (-A i) (A i))ᶜ,
          ‖QuantitativeSaddle.standardGaussian v * (p i).eval (v : ℂ)‖) ≤
          w i * ((b i)⁻¹ ^ (8 * (N + 1)) / A i) := by
            simpa only [w] using htail
        _ ≤ w i * rate i := by
          have hw : 0 ≤ w i := gaussianPolynomialTailWeight_nonneg _
          gcongr
          rw [div_eq_mul_inv]
          exact (mul_le_of_le_one_right (by positivity) hAinv).trans hpow
    have hleft0 : 0 ≤ (∫ v in (Icc (-A i) (A i))ᶜ,
        ‖QuantitativeSaddle.standardGaussian v * (p i).eval (v : ℂ)‖) :=
      integral_nonneg fun _ => norm_nonneg _
    have hright0 : 0 ≤ w i * rate i :=
      mul_nonneg (gaussianPolynomialTailWeight_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hleft0, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hright0]
    exact htail'
  have hproduct : (fun i => w i * rate i) =O[l] rate := by
    have hw : w =O[l] (fun _i => (1 : ℝ)) := by
      simpa only [w] using hweight
    simpa only [one_mul] using hw.mul (isBigO_refl rate l)
  simpa only [A, w, rate] using hdom.trans hproduct

end Fabius.SaddleExpansion
