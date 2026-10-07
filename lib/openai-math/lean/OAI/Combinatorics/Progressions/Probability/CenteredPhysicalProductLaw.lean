import OAI.Combinatorics.Progressions.Estimates.ShiftedProductTestError

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem shiftedSmoothProductMass_zero_pos {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) : 0 < shiftedSmoothProductMass 0 S := by
  rw [shiftedSmoothProductMass_eq_prod 0 S hS]
  apply Finset.prod_pos
  intro i _
  simpa only [shiftedSmoothSampleSum, Pi.zero_apply, sub_zero, smoothSampleSum] using
    smoothSampleSum_pos (hS i)

theorem smoothProductPMF_matrix_image {K X : Type*} [Fintype K] [Fintype X]
    {I : X → Type*} [∀ x, Fintype (I x)]
    (S : K × X → ℝ) (hS : ∀ z, 0 < S z) (M : ∀ x, Matrix (I x) K ℤ) :
    (smoothProductPMF S hS).map (fun z x => M x *ᵥ (fun k => z (k, x))) =
      dependentProductPMF (fun x => smoothMatrixImagePMF (M x) (fun k => S (k, x)) (fun k => hS (k, x))) := by
  have h := shiftedSmoothProductPMF_matrix_image (0 : K × X → ℝ) S hS
    (shiftedSmoothProductMass_zero_pos S hS) M
  have hz (x : X) : (fun k : K => (0 : K × X → ℝ) (k, x)) = 0 := rfl
  simpa only [hz, shiftedSmoothProductPMF_zero, smoothMatrixImagePMF] using h

theorem smoothProductPMF_matrix_image_scaled {K X : Type*} [Fintype K] [Fintype X]
    {I : X → Type*} [∀ x, Fintype (I x)]
    (S : K × X → ℝ) (hS : ∀ z, 0 < S z) (M : ∀ x, Matrix (I x) K ℤ)
    (P : ∀ x, I x → ℝ) (v : ∀ x, I x → ℤ) :
    (∏ x, ∏ i, P x i) *
        (((smoothProductPMF S hS).map (fun z x => M x *ᵥ (fun k => z (k, x)))) v).toReal =
      ∏ x, (∏ i, P x i) * (smoothMatrixImagePMF (M x) (fun k => S (k, x)) (fun k => hS (k, x)) (v x)).toReal := by
  rw [smoothProductPMF_matrix_image, dependentProductPMF_scaled]

end Erdos3

end

end OAI
