import OAI.Combinatorics.Progressions.Estimates.RationalHeight
import OAI.Combinatorics.Progressions.Geometry.NormalizedMinorCoordinates

namespace OAI

section

namespace Erdos3

theorem integer_row_normalization_entry {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (p : Fin k → ι) (hp : (Z.submatrix p id).det ≠ 0)
    (i : ι) (j : Fin k) :
    let H := Z.map (Int.castRingHom ℚ)
    (H * (H.submatrix p id)⁻¹) i j =
      ((Z.submatrix (Function.update p j i) id).det : ℚ) / ((Z.submatrix p id).det : ℚ) := by
  let H := Z.map (Int.castRingHom ℚ)
  have hdet (q : Fin k → ι) : (H.submatrix q id).det = ((Z.submatrix q id).det : ℚ) := by
    change ((Z.submatrix q id).map (Int.castRingHom ℚ)).det = _
    exact ((Int.castRingHom ℚ).map_det _).symm
  have hp' : (H.submatrix p id).det ≠ 0 := by rw [hdet]; exact_mod_cast hp
  change (H * (H.submatrix p id)⁻¹) i j = _
  calc
    _ = (H.submatrix (Function.update p j i) id).det / (H.submatrix p id).det :=
      row_normalization_entry H p hp' i j
    _ = _ := by rw [hdet, hdet]

theorem integer_row_normalization_height {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (p : Fin k → ι) (hp : (Z.submatrix p id).det ≠ 0)
    (N : ℕ) (hN : ∀ q : Fin k → ι, (Z.submatrix q id).det.natAbs ≤ N)
    (i : ι) (j : Fin k) :
    let H := Z.map (Int.castRingHom ℚ)
    RationalHeightLE ((H * (H.submatrix p id)⁻¹) i j) N := by
  dsimp only
  rw [integer_row_normalization_entry Z p hp i j]
  exact rationalHeightLE_fraction _ _ hp (hN _) (hN _)

end Erdos3

end

end OAI
