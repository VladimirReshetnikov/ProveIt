import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace OAI

section

namespace Erdos3

noncomputable def homogenizingMonomial {I R : Type*} [CommRing R]
    (h : ℕ) (d : I →₀ ℕ) : MvPolynomial (Option I) R :=
  MvPolynomial.X none ^ (h - d.degree) *
    MvPolynomial.rename some (MvPolynomial.monomial d 1)

noncomputable def dehomogenizingSubstitution {I R : Type*} [CommRing R] : Option I → MvPolynomial I R
  | none => 1
  | some i => MvPolynomial.X i

theorem homogenizingMonomial_homogeneous {I R : Type*} [CommRing R]
    (h : ℕ) (d : I →₀ ℕ) (hd : d.degree ≤ h) :
    (homogenizingMonomial (R := R) h d).IsHomogeneous h := by
  have hh := (MvPolynomial.isHomogeneous_X_pow (R := R) (none : Option I) (h - d.degree)).mul
    ((MvPolynomial.isHomogeneous_monomial (1 : R) (rfl : d.degree = d.degree)).rename_isHomogeneous
      (f := some))
  simpa only [homogenizingMonomial, Nat.sub_add_cancel hd] using hh

theorem homogenizingMonomial_dehomogenize {I R : Type*} [CommRing R]
    (h : ℕ) (d : I →₀ ℕ) :
    MvPolynomial.aeval (dehomogenizingSubstitution (R := R)) (homogenizingMonomial (R := R) h d) =
      MvPolynomial.monomial d (1 : R) := by
  simp only [homogenizingMonomial, map_mul, map_pow, MvPolynomial.aeval_X,
    dehomogenizingSubstitution, one_pow, one_mul, MvPolynomial.aeval_rename]
  exact MvPolynomial.aeval_X_left_apply _

end Erdos3

end

end OAI
