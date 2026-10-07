/- Modified for ProveIt: distribute polynomial coefficients over finite sums
explicitly on Lean 4.32. Mathematical statements are unchanged. -/
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

noncomputable def mapPolynomialCoefficients {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) : MvPolynomial I R :=
  ∑ d ∈ P.support, monomial d (L (P.coeff d))

theorem mapPolynomialCoefficients_coeff {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) (d : I →₀ ℕ) :
    (mapPolynomialCoefficients L P).coeff d = L (P.coeff d) := by
  by_cases hd : d ∈ P.support
  · simp [mapPolynomialCoefficients, MvPolynomial.coeff_sum, coeff_monomial, hd]
  · simp [mapPolynomialCoefficients, MvPolynomial.coeff_sum, coeff_monomial, hd, notMem_support_iff.mp hd]

theorem mapPolynomialCoefficients_degree {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) :
    (mapPolynomialCoefficients L P).totalDegree ≤ P.totalDegree := by
  unfold mapPolynomialCoefficients
  apply totalDegree_finsetSum_le
  intro d hd
  exact (totalDegree_monomial_le d _).trans (le_totalDegree hd)

theorem mapPolynomialCoefficients_eval {I R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (L : S →ₗ[R] R) (P : MvPolynomial I S) (x : I → R) :
    eval x (mapPolynomialCoefficients L P) = L (eval (fun i => algebraMap R S (x i)) P) := by
  unfold mapPolynomialCoefficients
  rw [map_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro d _
  have he : P.coeff d * d.prod (fun i n => (algebraMap R S) (x i) ^ n) =
      (d.prod (fun i n => x i ^ n)) • P.coeff d := by
    simp only [Finsupp.prod, Algebra.smul_def, map_prod, map_pow]
    exact mul_comm _ _
  rw [he, map_smul, smul_eq_mul, mul_comm]

end Erdos3

end

end OAI
