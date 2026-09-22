import Surreal.Algebra.PolynomialResidueGram

/-!
# The finite Bézout kernel

The polynomial identity `polynomial:eq:bezoutkernel` in
`docs/surcomplex/polynomial-algebra/article.tex`, over any commutative ring.
The two variables are represented by `R[X][X]`: the inner `X` is the source's
`z` and the outer `X` is its `Y`. Multiplication by `C X - X` expresses the
polynomial difference quotient without any division by a nonunit.

Its coefficient columns are the explicit residue-dual polynomials, so its
coefficient matrix is the inverse residue Gram matrix for a monic modulus.
Constants, degree zero, and the zero coefficient ring are included.
-/

namespace Surreal.FinitePolynomial

open Polynomial Finset

noncomputable section

variable {R : Type*} [CommRing R]

/-- The finite Bézout kernel `∑_{i<n} bⁱ(z) Y^i`. -/
def bezoutKernel (P : R[X]) : R[X][X] :=
  ∑ i ∈ range P.natDegree, C (dualPolynomial P i) * X ^ i

/-- Every coefficient column is the corresponding residue-dual polynomial.
The identity includes indices beyond the degree, where both sides vanish. -/
theorem coeff_bezoutKernel (P : R[X]) (i : ℕ) :
    (bezoutKernel P).coeff i = dualPolynomial P i := by
  simp only [bezoutKernel, finsetSum_coeff, coeff_C_mul_X_pow]
  simp only [sum_ite_eq, mem_range]
  split_ifs with hi
  · rfl
  · apply Polynomial.ext
    intro j
    rw [coeff_zero, coeff_dualPolynomial]
    exact (coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < j + i + 1)).symm

/-- Coefficient columns beyond the polynomial degree are zero. -/
theorem coeff_bezoutKernel_eq_zero (P : R[X]) {i : ℕ} (hi : P.natDegree ≤ i) :
    (bezoutKernel P).coeff i = 0 := by
  rw [coeff_bezoutKernel]
  ext j
  rw [coeff_dualPolynomial, coeff_zero]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The kernel's double coefficients are the shifted coefficients of `P`. -/
theorem coeff_coeff_bezoutKernel (P : R[X]) (i j : ℕ) :
    ((bezoutKernel P).coeff j).coeff i = P.coeff (i + j + 1) := by
  rw [coeff_bezoutKernel, coeff_dualPolynomial]

/-- The exact polynomial difference identity defining the Bézout kernel.
It requires neither monicity nor any inverse in the coefficient ring. -/
theorem sub_mul_bezoutKernel (P : R[X]) :
    (C (X : R[X]) - X) * bezoutKernel P = C P - P.map (C : R →+* R[X]) := by
  ext i j
  cases i <;> cases j <;>
    simp [sub_mul, coeff_sub, coeff_C_mul, coeff_C, coeff_map,
      coeff_X_mul, coeff_bezoutKernel, coeff_dualPolynomial, Nat.add_assoc]
  rw [sub_eq_zero]
  congr 1
  omega

/-- The kernel coefficient matrix is the matrix of explicit residue-dual columns. -/
theorem bezoutKernel_coefficientMatrix (P : R[X]) :
    (fun i j : Fin P.natDegree => ((bezoutKernel P).coeff j).coeff i) =
      dualCoefficientMatrix P := by
  funext i j
  rw [coeff_bezoutKernel, ← dualCoefficientMatrix_apply]

/-- The inverse-matrix clause of `polynomial:eq:bezoutkernel`, over the
original coefficient ring itself. -/
theorem residueGram_inv_eq_bezoutKernel_coefficientMatrix (P : R[X]) (hP : P.Monic) :
    (residueGram P hP)⁻¹ =
      (fun i j : Fin P.natDegree => ((bezoutKernel P).coeff j).coeff i) := by
  rw [bezoutKernel_coefficientMatrix, residueGram_inv_eq_dualCoefficientMatrix]

end

end Surreal.FinitePolynomial
