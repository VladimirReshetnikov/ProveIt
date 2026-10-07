import OAI.Combinatorics.Progressions.Estimates.SquarefreeExponents
import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def squarefreeCoefficients : VectorPolynomial ι ℚ L →ₗ[ℚ] (SquarefreeIndex ι → L) where
  toFun p a := coefficients p a.val
  map_add' p q := by ext a; simp only [map_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' r p := by ext a; simp only [map_smul, Finsupp.smul_apply, Pi.smul_apply, RingHom.id_apply]

@[simp] theorem squarefreeCoefficients_apply (p : VectorPolynomial ι ℚ L) (a : SquarefreeIndex ι) :
    squarefreeCoefficients p a = coefficients p a.val := rfl

theorem squarefreeCoefficients_monomial_self (a : SquarefreeIndex ι) (v : L) :
    squarefreeCoefficients (monomial a.val v) a = v := by
  classical
  simp only [squarefreeCoefficients_apply, coefficients_monomial, Finsupp.single_eq_same]

theorem squarefreeCoefficients_monomial_ne (a b : SquarefreeIndex ι) (h : a ≠ b) (v : L) :
    squarefreeCoefficients (monomial a.val v) b = 0 := by
  classical
  simp only [squarefreeCoefficients_apply, coefficients_monomial]
  exact Finsupp.single_eq_of_ne (fun he => h (Subtype.ext he.symm))

theorem squarefreeCoefficients_surjective [Fintype ι] :
    Function.Surjective (squarefreeCoefficients (ι := ι) (L := L)) := by
  classical
  intro f
  refine ⟨∑ a : SquarefreeIndex ι, monomial a.val (f a), ?_⟩
  ext b
  simp only [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single b]
  · exact squarefreeCoefficients_monomial_self b (f b)
  · intro a _ h
    exact squarefreeCoefficients_monomial_ne a b h (f a)
  · simp

theorem monomial_mem_squarefreeKernel (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) (v : L) :
    monomial a v ∈ LinearMap.ker (squarefreeCoefficients (ι := ι) (L := L)) := by
  classical
  change squarefreeCoefficients (monomial a v) = 0
  ext b
  simp only [squarefreeCoefficients_apply, coefficients_monomial, Pi.zero_apply]
  apply Finsupp.single_eq_of_ne
  intro he
  exact ha (he.symm ▸ b.property)

end Erdos3

end

end OAI
