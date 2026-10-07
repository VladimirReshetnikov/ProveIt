import OAI.Combinatorics.Progressions.Geometry.NormalizedMinorCoordinates
import OAI.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem row_normalization_abs_le {ι : Type*} {k : ℕ}
    (M : Matrix ι (Fin k) ℝ) (p : Fin k → ι)
    (hp : (M.submatrix p id).det ≠ 0) (C D : ℝ) (hD : 0 < D)
    (hminor : ∀ q : Fin k → ι, |(M.submatrix q id).det| ≤ C)
    (hlower : 1 / D ≤ |(M.submatrix p id).det|) (i : ι) (j : Fin k) :
    |(M * (M.submatrix p id)⁻¹) i j| ≤ C * D := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hminor p)
  calc
    _ = |(M.submatrix (Function.update p j i) id).det| /
        |(M.submatrix p id).det| := by rw [row_normalization_entry M p hp i j, abs_div]
    _ ≤ C / |(M.submatrix p id).det| :=
      div_le_div_of_nonneg_right (hminor _) (abs_nonneg _)
    _ ≤ C / (1 / D) := div_le_div_of_nonneg_left hC (one_div_pos.mpr hD) hlower
    _ = C * D := by rw [one_div, div_inv_eq_mul]

theorem euclidean_matrix_mulVec_norm_le {ι : Type*} [Fintype ι] {k : ℕ}
    (M : Matrix ι (Fin k) ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hM : ∀ i j, |M i j| ≤ H) (x : Fin k → ℝ) :
    ‖(EuclideanSpace.equiv ι ℝ).symm (M *ᵥ x)‖ ≤
      (Fintype.card ι : ℝ) * k * H * ‖x‖ := by
  have hi (i : ι) : |(M *ᵥ x) i| ≤ (k : ℝ) * H * ‖x‖ := by
    calc
      _ ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k, H * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hM i j)
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j) (abs_nonneg _) hH
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  calc
    _ ≤ ∑ i, |(M *ᵥ x) i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _i : ι, (k : ℝ) * H * ‖x‖ := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
