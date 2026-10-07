import OAI.Combinatorics.Progressions.Estimates.ArrayFunctionalSection
import OAI.Combinatorics.Progressions.Estimates.BoundedCoefficientExpansion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def boundedArrayPolynomial {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W) :
    VectorPolynomial K ℝ W := ∑ d, monomial d.val (x d)

theorem boundedArrayPolynomial_degreeLE {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W) :
    DegreeLE (1 : K → ℕ) h (boundedArrayPolynomial h x) := by
  intro e he
  rw [boundedArrayPolynomial, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro d _
  exact degreeLE_monomial_of_degree_le d.property (x d) e he

theorem boundedArrayPolynomial_coeff {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W)
    (d : BoundedCoefficientExponent K h) :
    coefficients (boundedArrayPolynomial h x) d.val = x d := by
  simp only [boundedArrayPolynomial, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e _ hed
    have he : e.val ≠ d.val := fun h => hed (Subtype.ext h)
    simp [he]
  · simp

theorem boundedArrayPolynomial_reconstruct {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ} (p : VectorPolynomial K ℝ W)
    (hp : DegreeLE (1 : K → ℕ) h p) :
    boundedArrayPolynomial h (fun d => coefficients p d.val) = p :=
  sum_bounded_monomial_coefficients p hp

theorem coefficientFunctional_boundedArrayPolynomial {K J : Type*} [Fintype K] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (frequency : (K →₀ ℕ) → J → ℝ)
    (x : BoundedCoefficientExponent K h → U) :
    coefficientFunctional frequency (map U.subtype (boundedArrayPolynomial h x)) =
      subspaceArrayFunctional U (fun d a => frequency d.val a) x := by
  simp only [boundedArrayPolynomial, map_sum, map_monomial, coefficientFunctional_monomial]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
