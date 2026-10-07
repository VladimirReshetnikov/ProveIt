import OAI.Combinatorics.Progressions.Estimates.IntegralHyperplaneCorrection

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem normalHyperplane_starProjection (ξ x : E) (hξ : ξ ≠ 0) :
    (normalFunctional ξ).ker.starProjection x =
      x - (inner ℝ ξ x / ‖ξ‖ ^ 2) • ξ := by
  have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hξ)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change inner ℝ ξ (x - (inner ℝ ξ x / ‖ξ‖ ^ 2) • ξ) = 0
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ hn, sub_self]
  · intro y hy
    have hy' : inner ℝ ξ y = 0 := hy
    rw [sub_sub_cancel, real_inner_smul_left, hy', mul_zero]

theorem normalHyperplane_height (ξ w : E) (hξ : ξ ≠ 0)
    (hw : inner ℝ ξ w = 1) :
    ‖w - (normalFunctional ξ).ker.starProjection w‖ = ‖ξ‖⁻¹ := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  rw [normalHyperplane_starProjection ξ w hξ, sub_sub_cancel, hw,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

end Erdos3

end

end OAI
