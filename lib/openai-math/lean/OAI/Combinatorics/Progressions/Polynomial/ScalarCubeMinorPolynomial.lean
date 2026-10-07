import OAI.Combinatorics.Progressions.Geometry.CoordinateDeterminant
import OAI.Combinatorics.Progressions.Sampling.ScalarCubeGridCoordinates

namespace OAI

section

namespace Erdos3

noncomputable def scalarCubeMinorPolynomial {I J : Type*} [Fintype I] [DecidableEq I]
    {N : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) : MvPolynomial (Fin N) ℝ :=
  (coordinateMatrixPolynomial (fun i j => e (s j, some i))).det

noncomputable def scalarCubeMinorTestPoint {I J : Type*} [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) : Fin N → ℝ := fun k =>
  match (e.symm k).2 with
  | none => 0
  | some i => if (e.symm k).1 = s i then 1 else 0

theorem scalarCubeMinorTestPoint_bound {I J : Type*} [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) (k : Fin N) :
    |scalarCubeMinorTestPoint e s k| ≤ 1 := by
  unfold scalarCubeMinorTestPoint
  split
  · norm_num
  · split_ifs <;> norm_num

theorem scalarCubeMinorPolynomial_test_value {I J : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq J] {N : ℕ}
    (e : J × Option I ≃ Fin N) (s : I → J) (hs : Function.Injective s) :
    MvPolynomial.eval (scalarCubeMinorTestPoint e s) (scalarCubeMinorPolynomial e s) = 1 := by
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval]
  have hm : ((fun i j => scalarCubeMinorTestPoint e s (e (s j, some i))) : Matrix I I ℝ) =
      (1 : Matrix I I ℝ) := by
    ext i j
    simp [scalarCubeMinorTestPoint, Matrix.one_apply, hs.eq_iff, eq_comm]
  rw [hm, Matrix.det_one]

noncomputable def normalizedScalarCubeMinor {I J : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} (s : I → J) (x : J → IntegerScalarCubeBox I L) : ℝ :=
  (((scalarCubeDifferenceMatrix x).submatrix id s).det : ℝ) / (L : ℝ) ^ Fintype.card I

theorem scalarCubeMinorPolynomial_grid_eval {I J : Type*} [Fintype I] [DecidableEq I]
    {N L : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    MvPolynomial.eval (fun i => (scalarCubeGrid e x i : ℝ) / L) (scalarCubeMinorPolynomial e s) =
      normalizedScalarCubeMinor s x := by
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval]
  let A := (scalarCubeDifferenceMatrix x).submatrix id s
  have hm : ((fun i j => (scalarCubeGrid e x (e (s j, some i)) : ℝ) / L) : Matrix I I ℝ) =
      (L : ℝ)⁻¹ • A.map (Int.castRingHom ℝ) := by
    ext i j
    simp [A, scalarCubeGrid, scalarCubeDifferenceMatrix, sampledColumnMatrix,
      Matrix.submatrix_apply, div_eq_mul_inv, mul_comm]
  have hcast : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det A).symm
  rw [hm, Matrix.det_smul, hcast, inv_pow]
  change ((L : ℝ) ^ Fintype.card I)⁻¹ * (A.det : ℝ) = (A.det : ℝ) / (L : ℝ) ^ Fintype.card I
  ring

end Erdos3

end

end OAI
