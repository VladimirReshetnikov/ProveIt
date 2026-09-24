import Surreal.Algebra.PolynomialResiduePairing
import Surreal.Algebra.PolynomialResidueGram
import Mathlib.RingTheory.Trace.Basic

/-!
# The trace Gram matrix in a monic polynomial quotient

The matrix identity in `polynomial:eq:tracegram` expresses the trace pairing
as the residue pairing followed by multiplication by the derivative.
It holds over an arbitrary commutative coefficient ring, without a
separability or reducedness assumption. Its determinant is the fixed
residue-Gram sign times the quotient norm of the derivative.

The identification of that norm with the polynomial resultant, and hence
this determinant with the native polynomial discriminant, is proved in
`PolynomialNormResultant`.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R : Type*} [CommRing R] (P : R[X]) (hP : P.Monic)

/-- The residue Gram entries are the residue pairing of power-basis vectors. -/
theorem residueGram_eq_pairing (i j : Fin P.natDegree) :
    residueGram P hP i j = residueFunctional P hP
      ((AdjoinRoot.powerBasisAux' hP) i * (AdjoinRoot.powerBasisAux' hP) j) := by
  have hb (k : Fin P.natDegree) : (AdjoinRoot.powerBasisAux' hP) k =
      AdjoinRoot.root P ^ (k : ℕ) := (AdjoinRoot.powerBasis' hP).basis_eq_pow k
  simp only [residueGram, hb, pow_add]

/-- The trace Gram matrix is the residue Gram matrix times the
multiplication matrix of the derivative, as in `polynomial:eq:tracegram`. -/
theorem quotient_traceMatrix_eq_residueGram_mul :
    Algebra.traceMatrix R (AdjoinRoot.powerBasisAux' hP) =
      residueGram P hP * Algebra.leftMulMatrix (AdjoinRoot.powerBasisAux' hP)
        (AdjoinRoot.mk P P.derivative) := by
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    quotient_trace_eq_residue_derivative P hP, Matrix.mul_apply]
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul, residueGram_eq_pairing]
  have h := congrArg
    (fun x => residueFunctional P hP ((AdjoinRoot.powerBasisAux' hP) i * x))
    ((AdjoinRoot.powerBasisAux' hP).sum_repr
      (AdjoinRoot.mk P P.derivative * (AdjoinRoot.powerBasisAux' hP) j))
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul] at h
  calc
    _ = residueFunctional P hP ((AdjoinRoot.powerBasisAux' hP) i *
        (AdjoinRoot.mk P P.derivative * (AdjoinRoot.powerBasisAux' hP) j)) := by
      congr 1
      ring
    _ = _ := by simpa only [mul_comm] using h.symm

/-- Taking determinants gives the residue sign times the quotient norm
of the derivative. The quotient may have nilpotents and the determinant
may vanish; no division is used. -/
theorem quotient_det_traceMatrix_eq_sign_mul_norm :
    (Algebra.traceMatrix R (AdjoinRoot.powerBasisAux' hP)).det =
      (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) *
        Algebra.norm R (AdjoinRoot.mk P P.derivative) := by
  rw [quotient_traceMatrix_eq_residueGram_mul, Matrix.det_mul, det_residueGram,
    ← Algebra.norm_eq_matrix_det (AdjoinRoot.powerBasisAux' hP)]

end

end Surreal.FinitePolynomial
