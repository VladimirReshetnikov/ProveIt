import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace DiophantineConsistency.QuadraticFiber
open Polynomial

/-- Only the selected exponent fibre matters; all other weights may collide. -/
theorem coeff_square_at_isolated {I R : Type*} [Fintype I] [DecidableEq I]
    [CommSemiring R] (w : I → ℕ) (u : I → R) (i j : I)
    (hiso : ∀ a b, w a + w b = w i + w j ↔
      (a = i ∧ b = j) ∨ (a = j ∧ b = i)) :
    ((∑ a, monomial (w a) (u a)) ^ 2).coeff (w i + w j) =
      if i = j then u i ^ 2 else 2 * u i * u j := by
  classical
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, finsetSum_coeff,
    monomial_mul_monomial, coeff_monomial]
  rw [Finset.sum_comm]
  simp_rw [hiso]
  by_cases h : i = j
  · subst j
    simp [ite_and]
  · simp only [ite_or, ite_and]
    simp_rw [Finset.sum_ite_irrel]
    simp +contextual only [h, if_false, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_ite]
    simp [Ne.symm h, Finset.filter_eq']
    ring

end DiophantineConsistency.QuadraticFiber
