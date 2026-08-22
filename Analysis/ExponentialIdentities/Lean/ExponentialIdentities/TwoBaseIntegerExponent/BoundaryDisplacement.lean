import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# Boundary displacement of a rectangular evaluation matrix

For the `K × K` exponent grid, multiplication of the evaluation columns by a
node coordinate agrees with shifting the corresponding exponent rows, except
on the terminal boundary.  This file proves the two exact displacement
identities and, over a field, shows that each displacement has rank exactly
`K` when the evaluation matrix and the relevant node coordinates are
nonzero.

This is only the finite matrix-algebra layer.  It does not formalize the
subsequent transfer-determinant or spectral-interpolation arguments.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Matrix

/-- The square `K × K` exponent/node grid. -/
abbrev GridIndex (K : ℕ) := Fin K × Fin K

/-- Evaluation of the two coordinate functions on the rectangular exponent grid. -/
def gridEvaluationMatrix {R : Type*} [CommSemiring R]
    (K : ℕ) (d₂ d₃ : GridIndex K → R) :
    Matrix (GridIndex K) (GridIndex K) R :=
  fun ij uv ↦ d₂ uv ^ (ij.1 : ℕ) * d₃ uv ^ (ij.2 : ℕ)

/-- Multiply each column of a square grid matrix by the corresponding scalar. -/
def scaleGridColumns {R : Type*} [Mul R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R)
    (d : GridIndex K → R) : Matrix (GridIndex K) (GridIndex K) R :=
  fun ij uv ↦ A ij uv * d uv

@[simp] theorem scaleGridColumns_eq_mul_diagonal {R : Type*} [Semiring R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R)
    (d : GridIndex K → R) :
    scaleGridColumns A d = A * Matrix.diagonal d := by
  ext ij uv
  simp [scaleGridColumns]

/-- Shift rows forward in the first exponent coordinate, inserting zero at the boundary. -/
def shiftFirstGridRows {R : Type*} [Zero R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R) :
    Matrix (GridIndex K) (GridIndex K) R :=
  fun ij uv ↦ if h : (ij.1 : ℕ) + 1 < K then
    A (⟨⟨(ij.1 : ℕ) + 1, h⟩, ij.2⟩) uv else 0

/-- Shift rows forward in the second exponent coordinate, inserting zero at the boundary. -/
def shiftSecondGridRows {R : Type*} [Zero R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R) :
    Matrix (GridIndex K) (GridIndex K) R :=
  fun ij uv ↦ if h : (ij.2 : ℕ) + 1 < K then
    A (⟨ij.1, ⟨(ij.2 : ℕ) + 1, h⟩⟩) uv else 0

/-- Retain only the terminal rows in the first exponent coordinate. -/
def firstGridBoundaryRows {R : Type*} [Zero R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R) :
    Matrix (GridIndex K) (GridIndex K) R :=
  fun ij uv ↦ if (ij.1 : ℕ) + 1 < K then 0 else A ij uv

/-- Retain only the terminal rows in the second exponent coordinate. -/
def secondGridBoundaryRows {R : Type*} [Zero R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R) :
    Matrix (GridIndex K) (GridIndex K) R :=
  fun ij uv ↦ if (ij.2 : ℕ) + 1 < K then 0 else A ij uv

/-- Diagonal projection onto the terminal first-coordinate boundary. -/
def firstGridBoundaryProjector {R : Type*} [Zero R] [One R]
    (K : ℕ) : Matrix (GridIndex K) (GridIndex K) R :=
  Matrix.diagonal fun ij ↦ if (ij.1 : ℕ) + 1 < K then 0 else 1

/-- Diagonal projection onto the terminal second-coordinate boundary. -/
def secondGridBoundaryProjector {R : Type*} [Zero R] [One R]
    (K : ℕ) : Matrix (GridIndex K) (GridIndex K) R :=
  Matrix.diagonal fun ij ↦ if (ij.2 : ℕ) + 1 < K then 0 else 1

/-- Matrix implementing the truncated first-coordinate row shift. -/
def firstGridShiftMatrix {R : Type*} [Zero R] [One R]
    (K : ℕ) : Matrix (GridIndex K) (GridIndex K) R :=
  fun ij kl ↦ if h : (ij.1 : ℕ) + 1 < K then
    if kl = ⟨⟨(ij.1 : ℕ) + 1, h⟩, ij.2⟩ then 1 else 0 else 0

/-- Matrix implementing the truncated second-coordinate row shift. -/
def secondGridShiftMatrix {R : Type*} [Zero R] [One R]
    (K : ℕ) : Matrix (GridIndex K) (GridIndex K) R :=
  fun ij kl ↦ if h : (ij.2 : ℕ) + 1 < K then
    if kl = ⟨ij.1, ⟨(ij.2 : ℕ) + 1, h⟩⟩ then 1 else 0 else 0

@[simp] theorem firstGridShiftMatrix_mul {R : Type*} [Semiring R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R) :
    firstGridShiftMatrix K * A = shiftFirstGridRows A := by
  ext ij uv
  by_cases h : (ij.1 : ℕ) + 1 < K
  · simp [firstGridShiftMatrix, shiftFirstGridRows, Matrix.mul_apply, h]
  · simp [firstGridShiftMatrix, shiftFirstGridRows, Matrix.mul_apply, h]

@[simp] theorem secondGridShiftMatrix_mul {R : Type*} [Semiring R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R) :
    secondGridShiftMatrix K * A = shiftSecondGridRows A := by
  ext ij uv
  by_cases h : (ij.2 : ℕ) + 1 < K
  · simp [secondGridShiftMatrix, shiftSecondGridRows, Matrix.mul_apply, h]
  · simp [secondGridShiftMatrix, shiftSecondGridRows, Matrix.mul_apply, h]

@[simp] theorem firstGridBoundaryProjector_mul {R : Type*} [Semiring R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R) :
    firstGridBoundaryProjector K * A = firstGridBoundaryRows A := by
  ext ij uv
  simp [firstGridBoundaryProjector, firstGridBoundaryRows]

@[simp] theorem secondGridBoundaryProjector_mul {R : Type*} [Semiring R]
    {K : ℕ} (A : Matrix (GridIndex K) (GridIndex K) R) :
    secondGridBoundaryProjector K * A = secondGridBoundaryRows A := by
  ext ij uv
  simp [secondGridBoundaryProjector, secondGridBoundaryRows]

private def terminalFin (K : ℕ) (hK : 0 < K) : Fin K :=
  ⟨K - 1, by omega⟩

private def firstBoundaryIndexEquiv (K : ℕ) (hK : 0 < K) :
    {ij : GridIndex K // ¬(ij.1 : ℕ) + 1 < K} ≃ Fin K where
  toFun ij := ij.1.2
  invFun j := ⟨⟨terminalFin K hK, j⟩, by simp [terminalFin]; omega⟩
  left_inv ij := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      simp [terminalFin]
      omega
    · rfl
  right_inv j := rfl

private def secondBoundaryIndexEquiv (K : ℕ) (hK : 0 < K) :
    {ij : GridIndex K // ¬(ij.2 : ℕ) + 1 < K} ≃ Fin K where
  toFun ij := ij.1.1
  invFun i := ⟨⟨i, terminalFin K hK⟩, by simp [terminalFin]; omega⟩
  left_inv ij := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [terminalFin]
      omega
  right_inv i := rfl

/-- The first-coordinate boundary projector has exactly `K` independent rows. -/
theorem rank_firstGridBoundaryProjector {R : Type*} [Field R] [DecidableEq R]
    (K : ℕ) (hK : 0 < K) :
    (firstGridBoundaryProjector (R := R) K).rank = K := by
  rw [firstGridBoundaryProjector, Matrix.rank_diagonal]
  let e : {ij : GridIndex K //
      (if (ij.1 : ℕ) + 1 < K then (0 : R) else 1) ≠ 0} ≃
      {ij : GridIndex K // ¬(ij.1 : ℕ) + 1 < K} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by simp)
  rw [Fintype.card_congr e, Fintype.card_congr (firstBoundaryIndexEquiv K hK)]
  exact Fintype.card_fin K

/-- The second-coordinate boundary projector has exactly `K` independent rows. -/
theorem rank_secondGridBoundaryProjector {R : Type*} [Field R] [DecidableEq R]
    (K : ℕ) (hK : 0 < K) :
    (secondGridBoundaryProjector (R := R) K).rank = K := by
  rw [secondGridBoundaryProjector, Matrix.rank_diagonal]
  let e : {ij : GridIndex K //
      (if (ij.2 : ℕ) + 1 < K then (0 : R) else 1) ≠ 0} ≃
      {ij : GridIndex K // ¬(ij.2 : ℕ) + 1 < K} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by simp)
  rw [Fintype.card_congr e, Fintype.card_congr (secondBoundaryIndexEquiv K hK)]
  exact Fintype.card_fin K

theorem rank_firstGridBoundaryRows {R : Type*} [Field R] [DecidableEq R]
    {K : ℕ} (hK : 0 < K) (A : Matrix (GridIndex K) (GridIndex K) R)
    (hA : IsUnit A.det) :
    (firstGridBoundaryRows A).rank = K := by
  rw [← firstGridBoundaryProjector_mul]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det A _ hA]
  exact rank_firstGridBoundaryProjector K hK

theorem rank_secondGridBoundaryRows {R : Type*} [Field R] [DecidableEq R]
    {K : ℕ} (hK : 0 < K) (A : Matrix (GridIndex K) (GridIndex K) R)
    (hA : IsUnit A.det) :
    (secondGridBoundaryRows A).rank = K := by
  rw [← secondGridBoundaryProjector_mul]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det A _ hA]
  exact rank_secondGridBoundaryProjector K hK

/-- Coordinatewise first-shift displacement, before replacing the operations by matrices. -/
theorem shiftFirst_gridEvaluationMatrix {R : Type*} [CommRing R]
    (K : ℕ) (d₂ d₃ : GridIndex K → R) :
    shiftFirstGridRows (gridEvaluationMatrix K d₂ d₃) -
        scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₂ =
      -firstGridBoundaryRows
        (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₂) := by
  ext ij uv
  by_cases h : (ij.1 : ℕ) + 1 < K
  · simp [shiftFirstGridRows, firstGridBoundaryRows,
      gridEvaluationMatrix, h, pow_succ]
    ring
  · simp [shiftFirstGridRows, firstGridBoundaryRows,
      gridEvaluationMatrix, h]

/-- Coordinatewise second-shift displacement, before replacing the operations by matrices. -/
theorem shiftSecond_gridEvaluationMatrix {R : Type*} [CommRing R]
    (K : ℕ) (d₂ d₃ : GridIndex K → R) :
    shiftSecondGridRows (gridEvaluationMatrix K d₂ d₃) -
        scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₃ =
      -secondGridBoundaryRows
        (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₃) := by
  ext ij uv
  by_cases h : (ij.2 : ℕ) + 1 < K
  · simp [shiftSecondGridRows, secondGridBoundaryRows,
      gridEvaluationMatrix, h, pow_succ]
    ring
  · simp [shiftSecondGridRows, secondGridBoundaryRows,
      gridEvaluationMatrix, h]

/-- Exact first-coordinate matrix displacement identity `S₂E - ED₂ = -P₂ED₂`. -/
theorem first_gridEvaluation_displacement {R : Type*} [CommRing R]
    (K : ℕ) (d₂ d₃ : GridIndex K → R) :
    firstGridShiftMatrix K * gridEvaluationMatrix K d₂ d₃ -
        gridEvaluationMatrix K d₂ d₃ * Matrix.diagonal d₂ =
      -(firstGridBoundaryProjector K *
        (gridEvaluationMatrix K d₂ d₃ * Matrix.diagonal d₂)) := by
  rw [firstGridShiftMatrix_mul, ← scaleGridColumns_eq_mul_diagonal,
    shiftFirst_gridEvaluationMatrix, firstGridBoundaryProjector_mul]

/-- Exact second-coordinate matrix displacement identity `S₃E - ED₃ = -P₃ED₃`. -/
theorem second_gridEvaluation_displacement {R : Type*} [CommRing R]
    (K : ℕ) (d₂ d₃ : GridIndex K → R) :
    secondGridShiftMatrix K * gridEvaluationMatrix K d₂ d₃ -
        gridEvaluationMatrix K d₂ d₃ * Matrix.diagonal d₃ =
      -(secondGridBoundaryProjector K *
        (gridEvaluationMatrix K d₂ d₃ * Matrix.diagonal d₃)) := by
  rw [secondGridShiftMatrix_mul, ← scaleGridColumns_eq_mul_diagonal,
    shiftSecond_gridEvaluationMatrix, secondGridBoundaryProjector_mul]

theorem rank_neg_matrix {R : Type*} [Field R]
    {m n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix m n R) : (-A).rank = A.rank := by
  rw [show -A = A * (-1 : Matrix n n R) by simp]
  apply Matrix.rank_mul_eq_left_of_isUnit_det (-1 : Matrix n n R) A
  rw [show (-1 : Matrix n n R) = -(1 : Matrix n n R) by rfl, Matrix.det_neg]
  simp

theorem rank_first_gridEvaluation_displacement {R : Type*} [Field R]
    [DecidableEq R] (K : ℕ) (hK : 0 < K) (d₂ d₃ : GridIndex K → R)
    (hdet : IsUnit (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₂).det) :
    (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₂ -
      shiftFirstGridRows (gridEvaluationMatrix K d₂ d₃)).rank = K := by
  have hEq :
      scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₂ -
          shiftFirstGridRows (gridEvaluationMatrix K d₂ d₃) =
        firstGridBoundaryRows
          (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₂) := by
    rw [← neg_sub, shiftFirst_gridEvaluationMatrix]
    simp
  rw [hEq]
  exact rank_firstGridBoundaryRows hK _ hdet

theorem rank_second_gridEvaluation_displacement {R : Type*} [Field R]
    [DecidableEq R] (K : ℕ) (hK : 0 < K) (d₂ d₃ : GridIndex K → R)
    (hdet : IsUnit (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₃).det) :
    (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₃ -
      shiftSecondGridRows (gridEvaluationMatrix K d₂ d₃)).rank = K := by
  have hEq :
      scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₃ -
          shiftSecondGridRows (gridEvaluationMatrix K d₂ d₃) =
        secondGridBoundaryRows
          (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₃) := by
    rw [← neg_sub, shiftSecond_gridEvaluationMatrix]
    simp
  rw [hEq]
  exact rank_secondGridBoundaryRows hK _ hdet

theorem rank_first_gridEvaluation_displacement_of_det_ne_zero
    {R : Type*} [Field R] [DecidableEq R]
    (K : ℕ) (hK : 0 < K) (d₂ d₃ : GridIndex K → R)
    (hE : (gridEvaluationMatrix K d₂ d₃).det ≠ 0)
    (hd₂ : ∀ uv, d₂ uv ≠ 0) :
    (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₂ -
      shiftFirstGridRows (gridEvaluationMatrix K d₂ d₃)).rank = K := by
  apply rank_first_gridEvaluation_displacement K hK d₂ d₃
  rw [scaleGridColumns_eq_mul_diagonal, Matrix.det_mul, Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr
    (mul_ne_zero hE (Finset.prod_ne_zero_iff.mpr fun uv _ ↦ hd₂ uv))

theorem rank_second_gridEvaluation_displacement_of_det_ne_zero
    {R : Type*} [Field R] [DecidableEq R]
    (K : ℕ) (hK : 0 < K) (d₂ d₃ : GridIndex K → R)
    (hE : (gridEvaluationMatrix K d₂ d₃).det ≠ 0)
    (hd₃ : ∀ uv, d₃ uv ≠ 0) :
    (scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₃ -
      shiftSecondGridRows (gridEvaluationMatrix K d₂ d₃)).rank = K := by
  apply rank_second_gridEvaluation_displacement K hK d₂ d₃
  rw [scaleGridColumns_eq_mul_diagonal, Matrix.det_mul, Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr
    (mul_ne_zero hE (Finset.prod_ne_zero_iff.mpr fun uv _ ↦ hd₃ uv))

/-- The first-coordinate displacement has rank exactly `K`, not merely at most `K`. -/
theorem rank_first_gridEvaluation_matrix_displacement
    {R : Type*} [Field R] [DecidableEq R]
    (K : ℕ) (hK : 0 < K) (d₂ d₃ : GridIndex K → R)
    (hE : (gridEvaluationMatrix K d₂ d₃).det ≠ 0)
    (hd₂ : ∀ uv, d₂ uv ≠ 0) :
    (firstGridShiftMatrix K * gridEvaluationMatrix K d₂ d₃ -
      gridEvaluationMatrix K d₂ d₃ * Matrix.diagonal d₂).rank = K := by
  rw [firstGridShiftMatrix_mul, ← scaleGridColumns_eq_mul_diagonal]
  rw [show shiftFirstGridRows (gridEvaluationMatrix K d₂ d₃) -
        scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₂ =
      -(scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₂ -
        shiftFirstGridRows (gridEvaluationMatrix K d₂ d₃)) by abel,
    rank_neg_matrix]
  exact rank_first_gridEvaluation_displacement_of_det_ne_zero K hK d₂ d₃ hE hd₂

/-- The second-coordinate displacement has rank exactly `K`, not merely at most `K`. -/
theorem rank_second_gridEvaluation_matrix_displacement
    {R : Type*} [Field R] [DecidableEq R]
    (K : ℕ) (hK : 0 < K) (d₂ d₃ : GridIndex K → R)
    (hE : (gridEvaluationMatrix K d₂ d₃).det ≠ 0)
    (hd₃ : ∀ uv, d₃ uv ≠ 0) :
    (secondGridShiftMatrix K * gridEvaluationMatrix K d₂ d₃ -
      gridEvaluationMatrix K d₂ d₃ * Matrix.diagonal d₃).rank = K := by
  rw [secondGridShiftMatrix_mul, ← scaleGridColumns_eq_mul_diagonal]
  rw [show shiftSecondGridRows (gridEvaluationMatrix K d₂ d₃) -
        scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₃ =
      -(scaleGridColumns (gridEvaluationMatrix K d₂ d₃) d₃ -
        shiftSecondGridRows (gridEvaluationMatrix K d₂ d₃)) by abel,
    rank_neg_matrix]
  exact rank_second_gridEvaluation_displacement_of_det_ne_zero K hK d₂ d₃ hE hd₃

end LeanProofs.TwoBaseIntegerExponent
