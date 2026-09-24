import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Norm.Defs

/-!
# Monic polynomial quotients and the residue functional

The finite algebra underlying `polynomial:eq:lambdadef` and
`polynomial:thm:trace` is Mathlib's `AdjoinRoot P`, over an arbitrary
commutative coefficient ring. Monic division gives the power-basis
coordinates without inverting coefficients. The multiplication matrix,
trace, and norm below use Mathlib's existing operations.

These formulas are prerequisites for residue duality and the universal
trace/resultant identities. They do not assume distinct or labelled roots,
or restrict the coefficient ring to a field.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {R : Type*} [CommRing R] (P : R[X]) (hP : P.Monic)

/-- The source's residue functional: the top coefficient of the unique
representative below the degree of the monic modulus. -/
def residueFunctional : AdjoinRoot P →ₗ[R] R :=
  (Polynomial.lcoeff R (P.natDegree - 1)).comp (AdjoinRoot.modByMonicHom hP)

/-- The functional on a polynomial representative is monic remainder
coefficient extraction, exactly `polynomial:eq:lambdadef`. -/
@[simp] theorem residueFunctional_mk (Q : R[X]) :
    residueFunctional P hP (AdjoinRoot.mk P Q) = (Q %ₘ P).coeff (P.natDegree - 1) :=
  rfl

/-- Coordinates in the native power basis are all remainder coefficients. -/
theorem quotient_powerBasis_repr (h : AdjoinRoot P) (i : Fin P.natDegree) :
    (AdjoinRoot.powerBasis' hP).basis.repr h i =
      (AdjoinRoot.modByMonicHom hP h).coeff i := rfl

/-- Every entry of multiplication by a class is a finite monic-division
calculation, including for nonreduced quotients. -/
theorem quotient_leftMulMatrix (Q : R[X]) (i j : Fin P.natDegree) :
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hP).basis (AdjoinRoot.mk P Q) i j =
      ((Q * X ^ (j : ℕ)) %ₘ P).coeff i := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, (AdjoinRoot.powerBasis' hP).basis_eq_pow]
  change (AdjoinRoot.powerBasis' hP).basis.repr
    (AdjoinRoot.mk P Q * AdjoinRoot.root P ^ (j : ℕ)) i = _
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul, quotient_powerBasis_repr,
    AdjoinRoot.modByMonicHom_mk]

include hP

/-- The trace of multiplication is the finite sum of the diagonal
remainder coefficients, over any commutative ring. -/
theorem quotient_trace_eq_sum (Q : R[X]) :
    Algebra.trace R (AdjoinRoot P) (AdjoinRoot.mk P Q) =
      ∑ i : Fin P.natDegree, ((Q * X ^ (i : ℕ)) %ₘ P).coeff i := by
  rw [Algebra.trace_eq_matrix_trace (AdjoinRoot.powerBasis' hP).basis, Matrix.trace]
  exact Finset.sum_congr rfl (fun i _ => quotient_leftMulMatrix P hP Q i i)

/-- The quotient-algebra norm is the determinant of the actual
multiplication matrix, explicitly in remainder coordinates. -/
theorem quotient_norm_eq_det (Q : R[X]) :
    Algebra.norm R (AdjoinRoot.mk P Q) =
      Matrix.det (fun i j : Fin P.natDegree => ((Q * X ^ (j : ℕ)) %ₘ P).coeff i) := by
  rw [Algebra.norm_eq_matrix_det (AdjoinRoot.powerBasis' hP).basis]
  congr 1
  ext i j
  exact quotient_leftMulMatrix P hP Q i j

/-- Scalar extension commutes with every monic remainder coefficient.
This is the coefficient-level reason integral inputs remain integral;
no inverse coefficient or root-separation denominator is used. -/
theorem map_monic_remainder_coeff {S : Type*} [CommRing S]
    (f : R →+* S) (Q : R[X]) (i : ℕ) :
    f ((Q %ₘ P).coeff i) = ((Q.map f) %ₘ (P.map f)).coeff i := by
  rw [← Polynomial.map_modByMonic f hP, Polynomial.coeff_map]

end

end Surreal.FinitePolynomial
