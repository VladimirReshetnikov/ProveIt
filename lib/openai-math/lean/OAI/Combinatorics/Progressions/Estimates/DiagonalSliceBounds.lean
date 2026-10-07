import OAI.Combinatorics.Progressions.Probability.DiagonalImageDensity

namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι]

theorem coordinateScaleEquiv_norm_le (w : ι → ℝ) (hw : ∀ i, w i ≠ 0)
    {C : ℝ} (hC : 0 ≤ C) (hcap : ∀ i, |w i| ≤ C) :
    ‖(coordinateScaleEquiv w hw).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg x))).2
  intro i
  change ‖w i * x i‖ ≤ C * ‖x‖
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (hcap i) (norm_le_pi_norm x i) (norm_nonneg _) hC

theorem coordinateScaleEquiv_inverse_norm_le (w : ι → ℝ) (hw : ∀ i, w i ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ i, δ ≤ |w i|) :
    ‖(coordinateScaleEquiv w hw).toContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ δ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hδ.le)
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (inv_nonneg.mpr hδ.le) (norm_nonneg x))).2
  intro i
  change ‖x i / w i‖ ≤ δ⁻¹ * ‖x‖
  rw [norm_div, Real.norm_eq_abs (w i), div_eq_mul_inv, mul_comm]
  exact mul_le_mul (inv_anti₀ hδ (hlow i)) (norm_le_pi_norm x i) (norm_nonneg _)
    (inv_nonneg.mpr hδ.le)

theorem coordinateScaleEquiv_scaled_inverse_norm_le (w : ι → ℝ) (hw : ∀ i, w i ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ i, δ ≤ |w i|) :
    δ * ‖(coordinateScaleEquiv w hw).toContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ 1 := by
  exact (mul_le_mul_of_nonneg_left (coordinateScaleEquiv_inverse_norm_le w hw hδ hlow) hδ.le).trans_eq
    (mul_inv_cancel₀ hδ.ne')

theorem coordinateScaleEquiv_affine_box (b w : ι → ℝ) (hw : ∀ i, w i ≠ 0)
    (hbox : ∀ i, |b i| + |w i| ≤ 1) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ∀ i, |(b + (coordinateScaleEquiv w hw).toContinuousLinearEquiv x) i| ≤ 1 := by
  intro i
  change |b i + w i * x i| ≤ 1
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  exact (add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) (hx i))).trans (hbox i)

end Erdos3

end

end OAI
