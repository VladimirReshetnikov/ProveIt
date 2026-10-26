import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace PairFiber

theorem sum_two_point_fiber {I R : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid R]
    (f : I → I → R) (i j : I) :
    (∑ a, ∑ b, if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then f a b else 0) =
      if i = j then f i i else f i j + f j i := by
  classical
  by_cases h : i = j
  · subst j
    simp [ite_and]
  · simp only [ite_or, ite_and]
    simp_rw [Finset.sum_ite_irrel]
    simp +contextual only [h, if_false, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_ite]
    simp [Ne.symm h, Finset.filter_eq']

open Polynomial

/-- Only the fibre of the selected exponent matters; other weights may collide. -/
theorem coeff_mul_at_isolated {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] (w : I → ℕ) (u v : I → R) (i j : I)
    (hiso : ∀ a b, w a + w b = w i + w j ↔
      (a = i ∧ b = j) ∨ (a = j ∧ b = i)) :
    ((∑ a, monomial (w a) (u a)) * ∑ b, monomial (w b) (v b)).coeff (w i + w j) =
      if i = j then u i * v i else u i * v j + u j * v i := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum, finsetSum_coeff,
    monomial_mul_monomial, coeff_monomial]
  rw [Finset.sum_comm]
  simp_rw [hiso]
  exact sum_two_point_fiber (fun a b => u a * v b) i j

theorem coeff_square_at_isolated {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] (w : I → ℕ) (u : I → R) (i j : I)
    (hiso : ∀ a b, w a + w b = w i + w j ↔
      (a = i ∧ b = j) ∨ (a = j ∧ b = i)) :
    ((∑ a, monomial (w a) (u a)) ^ 2).coeff (w i + w j) =
      if i = j then u i ^ 2 else 2 * u i * u j := by
  rw [pow_two, coeff_mul_at_isolated w u u i j hiso]
  split <;> ring

#print axioms sum_two_point_fiber
#print axioms coeff_mul_at_isolated
#print axioms coeff_square_at_isolated

end PairFiber
