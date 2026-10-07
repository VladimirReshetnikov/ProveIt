import Mathlib.Data.Finsupp.Option
import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
import OAI.Combinatorics.Progressions.Polynomial.HomogenizingMonomial

namespace OAI

section

namespace Erdos3

theorem some_degree_le {K : Type*} [Fintype K] (d : Option K →₀ ℕ) :
    d.some.degree ≤ d.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_option]
  simp only [Finsupp.some_apply]
  omega

theorem dehomogenize_monomial {K R : Type*} [CommRing R]
    (d : Option K →₀ ℕ) (c : R) :
    MvPolynomial.aeval dehomogenizingSubstitution (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d.some c := by
  rw [MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_option_index d _ (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)]
  simp only [dehomogenizingSubstitution, one_pow, one_mul, MvPolynomial.algebraMap_eq]
  exact MvPolynomial.monomial_eq.symm

theorem VectorPolynomial.dehomogenize_monomial {K R W : Type*}
    [CommRing R] [AddCommGroup W] [Module R W]
    (d : Option K →₀ ℕ) (w : W) :
    VectorPolynomial.substitute dehomogenizingSubstitution (VectorPolynomial.monomial (R := R) d w) =
      VectorPolynomial.monomial (R := R) d.some w := by
  simp only [VectorPolynomial.monomial, VectorPolynomial.substitute_tmul, Erdos3.dehomogenize_monomial]

end Erdos3

end

end OAI
