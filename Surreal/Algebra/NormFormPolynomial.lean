import Mathlib.RingTheory.Norm.Defs
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The norm form as a native multivariate polynomial

The polynomial prerequisite for `odg:thm:norm` and `odg:dec:thm:etale`.
Define it over the base ring by the determinant of multiplication by the
universal linear combination of a finite basis. Evaluation at base-ring
coordinates is the native algebra norm, without embedding the extension
algebra in the target of later polynomial evaluations.
-/

namespace Surreal.NormForm

open MvPolynomial Module

noncomputable section

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι]

/-- The multiplication matrix of a generic element in a chosen finite basis. -/
def genericMatrix (b : Basis ι R S) : Matrix ι ι (MvPolynomial ι R) :=
  fun i j => ∑ k, C (Algebra.leftMulMatrix b (b k) i j) * X k

/-- The native norm polynomial over the base ring. -/
def polynomial (b : Basis ι R S) : MvPolynomial ι R := (genericMatrix b).det

/-- Evaluation under any coefficient homomorphism is the determinant of the specialized matrix. -/
theorem eval₂_polynomial {A : Type*} [CommRing A] (b : Basis ι R S)
    (φ : R →+* A) (x : ι → A) :
    (polynomial b).eval₂ φ x =
      Matrix.det (fun i j => ∑ k, φ (Algebra.leftMulMatrix b (b k) i j) * x k) := by
  change (MvPolynomial.eval₂Hom φ x) (genericMatrix b).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [genericMatrix]

/-- Specializing at base-ring coordinates gives the native algebra norm of the basis sum. -/
theorem eval_polynomial (b : Basis ι R S) (x : ι → R) :
    (polynomial b).eval x = Algebra.norm R (∑ k, x k • b k) := by
  change (polynomial b).eval₂ (RingHom.id R) x = _
  rw [eval₂_polynomial, Algebra.norm_eq_matrix_det b]
  congr 1
  ext i j
  simp [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

end
end Surreal.NormForm
