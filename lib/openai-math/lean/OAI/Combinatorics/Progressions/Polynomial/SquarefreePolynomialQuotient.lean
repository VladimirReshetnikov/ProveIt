import Mathlib.LinearAlgebra.Isomorphisms
import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

abbrev SquarefreePolynomial (ι L : Type*) [LieRing L] [LieAlgebra ℚ L] :=
  VectorPolynomial ι ℚ L ⧸ (squarefreePolynomialIdeal (ι := ι) (L := L))

noncomputable def squarefreeMk : VectorPolynomial ι ℚ L →ₗ⁅ℚ⁆ SquarefreePolynomial ι L :=
  lieQuotientMap squarefreePolynomialIdeal

theorem squarefreeMk_surjective : Function.Surjective (squarefreeMk (ι := ι) (L := L)) :=
  lieQuotientMap_surjective _

theorem squarefreeMk_monomial_zero (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) (v : L) :
    squarefreeMk (monomial a v) = (0 : SquarefreePolynomial ι L) :=
  (lieQuotientMap_eq_zero _ _).mpr (monomial_mem_squarefreeKernel a ha v)

noncomputable def squarefreeMonomial (a : SquarefreeIndex ι) : L →ₗ[ℚ] SquarefreePolynomial ι L where
  toFun v := squarefreeMk (monomial a.val v)
  map_add' v w := by simp only [monomial, TensorProduct.tmul_add, map_add]
  map_smul' r v := by simp only [monomial, TensorProduct.tmul_smul, map_smul, RingHom.id_apply]

theorem squarefreeMonomial_apply (a : SquarefreeIndex ι) (v : L) :
    squarefreeMonomial a v = squarefreeMk (monomial a.val v) := rfl

noncomputable def squarefreePolynomialEquiv [Fintype ι] :
    SquarefreePolynomial ι L ≃ₗ[ℚ] (SquarefreeIndex ι → L) :=
  LinearMap.quotKerEquivOfSurjective (squarefreeCoefficients (ι := ι) (L := L))
    (squarefreeCoefficients_surjective (ι := ι) (L := L))

@[simp] theorem squarefreePolynomialEquiv_mk [Fintype ι] (p : VectorPolynomial ι ℚ L) :
    squarefreePolynomialEquiv (squarefreeMk p) = squarefreeCoefficients p := rfl

theorem squarefreePolynomialEquiv_monomial_self [Fintype ι] (a : SquarefreeIndex ι) (v : L) :
    squarefreePolynomialEquiv (squarefreeMonomial a v) a = v :=
  squarefreeCoefficients_monomial_self a v

theorem squarefreePolynomialEquiv_monomial_ne [Fintype ι]
    (a b : SquarefreeIndex ι) (hab : a ≠ b) (v : L) :
    squarefreePolynomialEquiv (squarefreeMonomial a v) b = 0 :=
  squarefreeCoefficients_monomial_ne a b hab v

theorem sum_squarefreeMonomial [Fintype ι] (x : SquarefreePolynomial ι L) :
    (∑ a : SquarefreeIndex ι, squarefreeMonomial a (squarefreePolynomialEquiv x a)) = x := by
  classical
  apply squarefreePolynomialEquiv.injective
  ext b
  simp only [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single b]
  · exact squarefreePolynomialEquiv_monomial_self b _
  · intro a _ h
    exact squarefreePolynomialEquiv_monomial_ne a b h _
  · simp

theorem squarefreePolynomial_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (SquarefreePolynomial ι L) (SquarefreePolynomial ι L) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (VectorPolynomial.lowerCentralSeries_eq_bot hnil) _

end Erdos3

end

end OAI
