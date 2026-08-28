import FabiusFunction.MomentHankelMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant construction of the up-measure's orthogonal polynomials

Stage two of the integration volume's *orthogonal-polynomial layer*
obligation: the orthogonal polynomials themselves, by the classical
bordered-Hankel determinant construction.

* `borderedHankel F n x` — the `(n+1) × (n+1)` matrix whose first `n`
  rows are the moment rows `(m_{i+j})_j` and whose last row is the
  monomial row `(1, x, …, xⁿ)`;
* `hankelOrthoValue F n x` — its determinant, the classical
  determinant representation `h_n·P_n(x)` of the orthogonal
  polynomial;
* `integral_hankelOrthoValue_mul_pow` — **the orthogonality
  relations**: `∫ P_n(x)·x^{j} dμ_up = 0` for every `j < n`.  The
  proof is the classical one made formal: expanding along the last
  row turns the integral into the determinant of the matrix whose
  last row is the `j`-shifted moment row, which duplicates row `j`.
-/

set_option autoImplicit false

open MeasureTheory Matrix

namespace Fabius

/-- The bordered Hankel matrix: moment rows on top, the monomial row
at the bottom. -/
noncomputable def borderedHankel (F : BoundedFabius) (n : ℕ) (x : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) < n then upMoment F ((i : ℕ) + j) else x ^ (j : ℕ)

/-- The determinant orthogonal-polynomial values `h_n·P_n(x)`. -/
noncomputable def hankelOrthoValue (F : BoundedFabius) (n : ℕ)
    (x : ℝ) : ℝ :=
  (borderedHankel F n x).det

/-- The comparison matrix whose last row is the `j'`-shifted moment
row. -/
noncomputable def momentBordered (F : BoundedFabius) (n j' : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) < n then upMoment F ((i : ℕ) + j)
    else upMoment F ((j : ℕ) + j')

/-- For `j' < n` the comparison matrix has a duplicated row, so its
determinant vanishes. -/
theorem det_momentBordered_eq_zero (F : BoundedFabius) (n : ℕ)
    {j' : ℕ} (hj : j' < n) :
    (momentBordered F n j').det = 0 := by
  refine Matrix.det_zero_of_row_eq
    (i := (⟨j', by omega⟩ : Fin (n + 1))) (j := Fin.last n) ?_ ?_
  · intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_last] at hval
    omega
  · funext col
    show (if j' < n then upMoment F (j' + col) else _) =
      (if (Fin.last n : ℕ) < n then upMoment F ((Fin.last n : ℕ) + col)
        else upMoment F ((col : ℕ) + j'))
    rw [if_pos hj, if_neg (by simp [Fin.val_last]), Nat.add_comm]

/-- The last-row minors of the bordered matrix are `x`-free: they
agree with the minors of the comparison matrix. -/
theorem submatrix_borderedHankel_eq (F : BoundedFabius) (n : ℕ)
    (x : ℝ) (j' : ℕ) (j : Fin (n + 1)) :
    (borderedHankel F n x).submatrix (Fin.last n).succAbove
        j.succAbove =
      (momentBordered F n j').submatrix (Fin.last n).succAbove
        j.succAbove := by
  ext i' col'
  simp only [Matrix.submatrix_apply, Fin.succAbove_last]
  have hlt : ((Fin.castSucc i' : Fin (n + 1)) : ℕ) < n := by
    simpa using i'.isLt
  show (if ((Fin.castSucc i' : Fin (n + 1)) : ℕ) < n then _ else _) =
    (if ((Fin.castSucc i' : Fin (n + 1)) : ℕ) < n then _ else _)
  rw [if_pos hlt, if_pos hlt]

/-- **The orthogonality relations**: the determinant polynomial is
orthogonal to every lower monomial, `∫ P_n(x)·x^{j'} dμ_up = 0` for
`j' < n`. -/
theorem integral_hankelOrthoValue_mul_pow (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {j' : ℕ} (hj : j' < n) :
    ∫ x, hankelOrthoValue F n x * x ^ j' ∂(rvachevMeasure F) = 0 := by
  have hlastrow : ∀ (x : ℝ) (j : Fin (n + 1)),
      borderedHankel F n x (Fin.last n) j = x ^ (j : ℕ) := by
    intro x j
    show (if (Fin.last n : ℕ) < n then upMoment F _ else x ^ (j : ℕ)) =
      x ^ (j : ℕ)
    rw [if_neg (by simp [Fin.val_last])]
  have hexpand : (fun x : ℝ => hankelOrthoValue F n x * x ^ j') =
      fun x : ℝ => ∑ j : Fin (n + 1),
        ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
          ((momentBordered F n j').submatrix (Fin.last n).succAbove
            j.succAbove).det) * x ^ ((j : ℕ) + j') := by
    funext x
    rw [hankelOrthoValue, Matrix.det_succ_row _ (Fin.last n),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlastrow x j, submatrix_borderedHankel_eq F n x j' j, pow_add]
    ring
  rw [hexpand, integral_finsetSum _ fun j _ =>
    (integrable_pow_rvachevMeasure F hF _).const_mul _]
  have hsum : ∀ j : Fin (n + 1),
      ∫ x, ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
        ((momentBordered F n j').submatrix (Fin.last n).succAbove
          j.succAbove).det) * x ^ ((j : ℕ) + j')
        ∂(rvachevMeasure F) =
      ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
        ((momentBordered F n j').submatrix (Fin.last n).succAbove
          j.succAbove).det) * upMoment F ((j : ℕ) + j') := by
    intro j
    rw [MeasureTheory.integral_const_mul]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hsum j]
  have hdet := Matrix.det_succ_row (momentBordered F n j') (Fin.last n)
  have hlast : ∀ j : Fin (n + 1),
      momentBordered F n j' (Fin.last n) j =
        upMoment F ((j : ℕ) + j') := by
    intro j
    show (if (Fin.last n : ℕ) < n then upMoment F _
      else upMoment F ((j : ℕ) + j')) = upMoment F ((j : ℕ) + j')
    rw [if_neg (by simp [Fin.val_last])]
  calc ∑ j : Fin (n + 1),
        ((-1 : ℝ) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
          ((momentBordered F n j').submatrix (Fin.last n).succAbove
            j.succAbove).det) * upMoment F ((j : ℕ) + j')
      = (momentBordered F n j').det := by
        rw [hdet]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hlast j]
        ring
    _ = 0 := det_momentBordered_eq_zero F n hj

end Fabius
