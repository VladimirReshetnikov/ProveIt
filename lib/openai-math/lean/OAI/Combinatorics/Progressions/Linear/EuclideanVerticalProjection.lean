import OAI.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates

namespace OAI

section

namespace Erdos3

noncomputable def euclideanVerticalProjection {σ κ : Type*} :
    EuclideanSpace ℝ (σ ⊕ κ) →ₗ[ℝ] EuclideanSpace ℝ κ :=
  (EuclideanSpace.equiv κ ℝ).symm.toLinearMap.comp
    ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)

@[simp] theorem euclideanVerticalProjection_apply {σ κ : Type*}
    (x : EuclideanSpace ℝ (σ ⊕ κ)) (j : κ) :
    euclideanVerticalProjection x j = x (Sum.inr j) := rfl

theorem euclideanVerticalProjection_norm_le {σ κ : Type*} [Fintype σ] [Fintype κ]
    (x : EuclideanSpace ℝ (σ ⊕ κ)) : ‖euclideanVerticalProjection x‖ ≤ ‖x‖ := by
  have hs : ‖euclideanVerticalProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    simp only [euclideanVerticalProjection_apply]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => sq_nonneg ‖x (Sum.inl i)‖))
  nlinarith [norm_nonneg (euclideanVerticalProjection x), norm_nonneg x]

end Erdos3

end

end OAI
