import Surreal.Algebra.PolynomialResidueDual
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Determinant of the residue Gram matrix

The constant determinant `polynomial:eq:gramdet` in
`docs/surcomplex/polynomial-algebra/article.tex` holds over every commutative
coefficient ring, including at repeated roots. Reversing the columns turns
the residue Gram matrix into a lower triangular matrix with diagonal one.
The empty matrix in degree zero satisfies the same identity.
-/

namespace Surreal.FinitePolynomial

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R]

/-- The residue Gram matrix in the quotient power basis. -/
def residueGram (P : R[X]) (hP : P.Monic) : Matrix (Fin P.natDegree) (Fin P.natDegree) R :=
  fun i j => residueFunctional P hP (AdjoinRoot.root P ^ ((i : ℕ) + j))

/-- The entries before the antidiagonal vanish. -/
theorem residueGram_entry_eq_zero (P : R[X]) (hP : P.Monic)
    (i j : Fin P.natDegree) (hij : (i : ℕ) + j < P.natDegree - 1) :
    residueGram P hP i j = 0 := by
  nontriviality R
  unfold residueGram
  rw [← AdjoinRoot.mk_X, ← map_pow, residueFunctional_mk,
    (modByMonic_eq_self_iff hP).mpr (by
      rw [degree_X_pow, degree_eq_natDegree hP.ne_zero]
      exact_mod_cast (show (i : ℕ) + j < P.natDegree by omega)),
    coeff_X_pow, if_neg (by omega)]

/-- Each antidiagonal entry is one, independently of the coefficients. -/
theorem residueGram_entry_eq_one (P : R[X]) (hP : P.Monic)
    (i j : Fin P.natDegree) (hij : (i : ℕ) + j = P.natDegree - 1) :
    residueGram P hP i j = 1 := by
  nontriviality R
  unfold residueGram
  rw [← AdjoinRoot.mk_X, ← map_pow, residueFunctional_mk,
    (modByMonic_eq_self_iff hP).mpr (by
      rw [degree_X_pow, degree_eq_natDegree hP.ne_zero]
      exact_mod_cast (show (i : ℕ) + j < P.natDegree by omega)),
    coeff_X_pow, if_pos hij.symm]

private theorem cast_sign_revPerm (n : ℕ) :
    (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) : ℤ) : R) =
      (-1 : R) ^ (n * (n - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  simp only [Units.coe_prod, Int.cast_prod, apply_ite, Units.val_one, Units.val_neg,
    Int.cast_one, Int.cast_neg]
  have hprod (j : Fin n) :
      (∏ i ∈ Iio j, if Fin.revPerm i < Fin.revPerm j then (1 : R) else -1) =
        (-1 : R) ^ (j : ℕ) := by
    calc
      _ = ∏ _i ∈ Iio j, (-1 : R) := by
        apply prod_congr rfl
        intro i hi
        rw [if_neg]
        simpa only [Fin.revPerm_apply, Fin.rev_lt_rev] using
          (not_lt_of_gt (mem_Iio.mp hi))
      _ = _ := by rw [prod_const, Fin.card_Iio]
  simp_rw [hprod]
  change (∏ j : Fin n, (-1 : R) ^ (j : ℕ)) = _
  have hsum : (∑ j : Fin n, (j : ℕ)) = n * (n - 1) / 2 := by
    simpa only [sum_range_id] using (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n)
  exact (Finset.prod_pow_eq_pow_sum univ (fun j : Fin n => (j : ℕ)) (-1 : R)).trans
    (congrArg (fun k : ℕ => (-1 : R) ^ k) hsum)

/-- The Gram determinant is the sign of column reversal, exactly
`polynomial:eq:gramdet`. No discriminant or root separation is inverted. -/
theorem det_residueGram (P : R[X]) (hP : P.Monic) :
    (residueGram P hP).det = (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) := by
  let M := (residueGram P hP).submatrix id Fin.revPerm
  have htri : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    change residueGram P hP i j.rev = 0
    apply residueGram_entry_eq_zero
    simp only [Fin.val_rev]
    omega
  have hdiag (i : Fin P.natDegree) : M i i = 1 := by
    change residueGram P hP i i.rev = 1
    apply residueGram_entry_eq_one
    simp only [Fin.val_rev]
    omega
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_lowerTriangular M htri]
    simp_rw [hdiag]
    exact prod_const_one
  have heq := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin P.natDegree))
    (residueGram P hP)
  change M.det = _ at heq
  rw [hdet, cast_sign_revPerm] at heq
  have hsign : (-1 : R) ^ (P.natDegree * (P.natDegree - 1) / 2) *
      (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc
    _ = ((-1 : R) ^ (P.natDegree * (P.natDegree - 1) / 2) *
        (-1) ^ (P.natDegree * (P.natDegree - 1) / 2)) * (residueGram P hP).det := by
      rw [hsign, one_mul]
    _ = _ := by rw [mul_assoc, ← heq, mul_one]

/-- The coefficient columns of the explicit residue-dual polynomials.
This is also the coefficient matrix of the source's Bézout kernel. -/
def dualCoefficientMatrix (P : R[X]) : Matrix (Fin P.natDegree) (Fin P.natDegree) R :=
  fun i j => P.coeff ((i : ℕ) + j + 1)

theorem dualCoefficientMatrix_apply (P : R[X]) (i j : Fin P.natDegree) :
    dualCoefficientMatrix P i j = (dualPolynomial P j).coeff i :=
  (coeff_dualPolynomial P j i).symm

private theorem dualPolynomial_quotient_repr (P : R[X]) (hP : P.Monic)
    (i j : Fin P.natDegree) :
    (AdjoinRoot.powerBasis' hP).basis.repr (AdjoinRoot.mk P (dualPolynomial P j)) i =
      dualCoefficientMatrix P i j := by
  nontriviality R
  rw [quotient_powerBasis_repr, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff hP).mpr (by
      rw [degree_eq_natDegree hP.ne_zero, degree_lt_iff_coeff_zero]
      intro k hk
      rw [coeff_dualPolynomial]
      exact coeff_eq_zero_of_natDegree_lt (by omega)),
    ← dualCoefficientMatrix_apply]

/-- The explicit dual coefficient matrix is a right inverse of the
residue Gram matrix over the coefficient ring itself. -/
theorem residueGram_mul_dualCoefficientMatrix (P : R[X]) (hP : P.Monic) :
    residueGram P hP * dualCoefficientMatrix P = 1 := by
  ext i j
  let b := (AdjoinRoot.powerBasis' hP).basis
  let d := AdjoinRoot.mk P (dualPolynomial P j)
  calc
    _ = ∑ k : Fin P.natDegree,
        residueFunctional P hP (AdjoinRoot.root P ^ (i : ℕ) * b k) * b.repr d k := by
      simp only [Matrix.mul_apply, b, d, (AdjoinRoot.powerBasis' hP).basis_eq_pow,
        AdjoinRoot.powerBasis'_gen, ← pow_add, dualPolynomial_quotient_repr, residueGram]
    _ = residueFunctional P hP (AdjoinRoot.root P ^ (i : ℕ) * d) := by
      conv_rhs => rw [← b.sum_repr d]
      rw [Finset.mul_sum, map_sum]
      apply sum_congr rfl
      intro k _
      rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
    _ = _ := by
      dsimp only [d]
      simp only [residueFunctional_root_pow_mul_dualPolynomial, Matrix.one_apply, eq_comm]

/-- The explicit coefficient matrix equals the inverse Gram matrix,
the inverse-matrix assertion following `polynomial:eq:bezoutkernel`.
Its entries are polynomial coefficients, without any division. -/
theorem residueGram_inv_eq_dualCoefficientMatrix (P : R[X]) (hP : P.Monic) :
    (residueGram P hP)⁻¹ = dualCoefficientMatrix P :=
  Matrix.inv_eq_right_inv (residueGram_mul_dualCoefficientMatrix P hP)

end

end Surreal.FinitePolynomial
