import OAI.Combinatorics.Progressions.Estimates.DehomogenizedExponent
import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineLiftFrequency {K J A : Type*}
    (frequency : (K →₀ ℕ) → J → A) (d : Option K →₀ ℕ) : J → A := frequency d.some

theorem affineModeLift_coefficientFunctional {K J : Type*} [Fintype J]
    (frequency : (K →₀ ℕ) → J → ℝ) :
    affineModeLift (coefficientFunctional frequency) =
      coefficientFunctional (affineLiftFrequency frequency) := by
  apply LinearMap.ext
  intro p
  conv_lhs => rw [← sum_monomial_coefficients p]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, affineModeLift, LinearMap.comp_apply,
    dehomogenize_monomial, coefficientFunctional_monomial, affineLiftFrequency]

theorem affineModeLift_integerFrequency {K J : Type*} [Fintype J]
    (frequency : (K →₀ ℕ) → J → ℤ) :
    affineModeLift (coefficientFunctional (fun d j => (frequency d j : ℝ))) =
      coefficientFunctional (fun d j => ((affineLiftFrequency frequency d j : ℤ) : ℝ)) :=
  affineModeLift_coefficientFunctional _

theorem affineLiftFrequency_bound {K J : Type*} [Fintype K]
    (frequency : (K →₀ ℕ) → J → ℤ) {h : ℕ} {C : ℝ}
    (hbound : ∀ d, d.degree ≤ h → ∀ j, |(frequency d j : ℝ)| ≤ C) :
    ∀ d, d.degree = h → ∀ j, |((affineLiftFrequency frequency d j : ℤ) : ℝ)| ≤ C := by
  intro d hd j
  exact hbound d.some ((some_degree_le d).trans hd.le) j

end Erdos3.VectorPolynomial

end

end OAI
