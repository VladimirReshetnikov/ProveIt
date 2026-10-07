/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Algebra.MvPolynomial.Eval

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {V W R : Type*} [CommSemiring R]

noncomputable def polynomialOfFiniteCoefficientVector (S : Finset (V →₀ ℕ))
    (c : S → R) : MvPolynomial V R :=
  ∑ α : S, MvPolynomial.monomial α.val (c α)

theorem polynomialOfFiniteCoefficientVector_coeff (S : Finset (V →₀ ℕ))
    (c : S → R) (α : S) :
    (polynomialOfFiniteCoefficientVector S c).coeff α.val = c α := by
  classical
  rw [polynomialOfFiniteCoefficientVector, coeff_sum, Finset.sum_eq_single α]
  · simp
  · intro β _ hβα
    rw [coeff_monomial, ite_eq_right]
    exact fun h => hβα (Subtype.ext h)
  · simp

theorem polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem
    (S : Finset (V →₀ ℕ)) (c : S → R) (β : V →₀ ℕ) (hβ : β ∉ S) :
    (polynomialOfFiniteCoefficientVector S c).coeff β = 0 := by
  classical
  rw [polynomialOfFiniteCoefficientVector, coeff_sum]
  apply Finset.sum_eq_zero
  intro α _
  rw [coeff_monomial, ite_eq_right]
  exact fun h => hβ (h ▸ α.property)

theorem polynomialOfFiniteCoefficientVector_support_subset (S : Finset (V →₀ ℕ))
    (c : S → R) : (polynomialOfFiniteCoefficientVector S c).support ⊆ S := by
  classical
  intro β hβ
  by_contra hout
  exact (MvPolynomial.mem_support_iff.mp hβ)
    (polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem S c β hout)

theorem polynomialOfFiniteCoefficientVector_reconstruct (S : Finset (V →₀ ℕ))
    (P : MvPolynomial V R) (hP : P.support ⊆ S) :
    polynomialOfFiniteCoefficientVector S (fun exponent => P.coeff exponent.val) = P := by
  classical
  ext β
  by_cases hβ : β ∈ S
  · exact polynomialOfFiniteCoefficientVector_coeff S _ ⟨β, hβ⟩
  · rw [polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem S _ β hβ]
    exact (MvPolynomial.notMem_support_iff.mp (fun h => hβ (hP h))).symm

theorem polynomialOfFiniteCoefficientVector_aeval_coeff (S : Finset (V →₀ ℕ))
    (c : S → R) (f : V → MvPolynomial W R) (β : W →₀ ℕ) :
    (MvPolynomial.aeval f (polynomialOfFiniteCoefficientVector S c)).coeff β =
      ∑ α : S, (MvPolynomial.aeval f (MvPolynomial.monomial α.val 1)).coeff β * c α := by
  classical
  rw [polynomialOfFiniteCoefficientVector, map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro α _
  simp only [aeval_monomial, MvPolynomial.algebraMap_eq, map_one, one_mul, coeff_C_mul]
  exact mul_comm _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem coeff_aeval_of_support_subset {V W R : Type*} [CommSemiring R]
    (S : Finset (V →₀ ℕ)) (P : MvPolynomial V R) (hP : P.support ⊆ S)
    (f : V → MvPolynomial W R) (β : W →₀ ℕ) :
    (MvPolynomial.aeval f P).coeff β =
      ∑ α : S, (MvPolynomial.aeval f (MvPolynomial.monomial α.val 1)).coeff β *
        P.coeff α.val := by
  calc
    _ = (MvPolynomial.aeval f
        (polynomialOfFiniteCoefficientVector S (fun exponent => P.coeff exponent.val))).coeff β :=
      congrArg (fun polynomial => (MvPolynomial.aeval f polynomial).coeff β)
        (polynomialOfFiniteCoefficientVector_reconstruct S P hP).symm
    _ = _ := polynomialOfFiniteCoefficientVector_aeval_coeff S
      (fun exponent => P.coeff exponent.val) f β

end Erdos3

end

end OAI
