import OAI.Combinatorics.Progressions.Polynomial.PolynomialKernelValues

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem DegreeLE.smul {I V : Type*} [AddCommGroup V] [Module ℝ V]
    {w : I → ℕ} {d : ℕ} {p : VectorPolynomial I ℝ V}
    (hp : DegreeLE w d p) (r : ℝ) : DegreeLE w d (r • p) := by
  intro α hα
  simp only [map_smul, Finsupp.smul_apply, hp α hα, smul_zero]

theorem coefficients_smul_mem {I J : Type*} (U : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) (hm : ∀ d, coefficients p d ∈ U) (r : ℝ) :
    ∀ d, coefficients (r • p) d ∈ U := by
  intro d
  simpa only [map_smul, Finsupp.smul_apply] using U.smul_mem r (hm d)

theorem integerRowPolynomial_smul {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (r : ℝ) :
    integerRowPolynomial a (r • p) = r • integerRowPolynomial a p := by
  ext α
  simp only [integerRowPolynomial_coeff, MvPolynomial.coeff_smul, map_smul,
    Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

end Erdos3.VectorPolynomial

end

end OAI
