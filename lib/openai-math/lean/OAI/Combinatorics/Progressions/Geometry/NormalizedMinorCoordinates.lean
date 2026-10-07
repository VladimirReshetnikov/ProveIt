import OAI.Combinatorics.Progressions.Estimates.LowerTriangularMinor

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem row_normalization_entry {K ι : Type*} [Field K] {k : ℕ}
    (H : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0)
    (i : ι) (j : Fin k) :
    (H * (H.submatrix p id)⁻¹) i j =
      (H.submatrix (Function.update p j i) id).det / (H.submatrix p id).det := by
  have h := row_minor_update_det H p (H * (H.submatrix p id)⁻¹)
    (Matrix.nonsing_inv_mul_cancel_right (H.submatrix p id) H (isUnit_iff_ne_zero.mpr hp)) i j
  exact (eq_div_iff hp).mpr h.symm

theorem row_normalization_submatrix {K ι : Type*} [Field K] {k : ℕ}
    (H : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0) :
    (H * (H.submatrix p id)⁻¹).submatrix p id = 1 := by
  rw [Matrix.submatrix_mul H (H.submatrix p id)⁻¹ p id id Function.bijective_id,
    Matrix.submatrix_id_id]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp)

theorem row_normalization_col_span {K ι : Type*} [Field K] {k : ℕ}
    (H : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0) :
    Submodule.span K (Set.range (H * (H.submatrix p id)⁻¹).col) =
      Submodule.span K (Set.range H.col) := by
  let B := H.submatrix p id
  have hsurj : Function.Surjective B⁻¹.mulVecLin := by
    intro x
    refine ⟨B *ᵥ x, ?_⟩
    change B⁻¹ *ᵥ (B *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hp),
      Matrix.one_mulVec]
  rw [← Matrix.range_mulVecLin, ← Matrix.range_mulVecLin, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)

end Erdos3

end

end OAI
