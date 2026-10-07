/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sigma_card_le_budget {α : Type*} [Fintype α] {κ : α → Type*}
    [∀ a, Fintype (κ a)] {p : ℝ} (hp : 0 ≤ p)
    (hα : (Fintype.card α : ℝ) ≤ p) (hκ : ∀ a, (Fintype.card (κ a) : ℝ) ≤ p) :
    (Fintype.card (Σ a, κ a) : ℝ) ≤ p ^ 2 := by
  classical
  calc
    _ = ∑ a, (Fintype.card (κ a) : ℝ) := by rw [Fintype.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _a : α, p := Finset.sum_le_sum (fun a _ => hκ a)
    _ = (Fintype.card α : ℝ) * p := by simp
    _ ≤ p * p := mul_le_mul_of_nonneg_right hα hp
    _ = p ^ 2 := by ring

theorem product_denominator_le_budget {α : Type*} [Fintype α] (m : α → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hα : (Fintype.card α : ℝ) ≤ p)
    (hm : ∀ a, (m a : ℝ) ≤ Real.exp p) :
    ((∏ a, m a : ℕ) : ℝ) ≤ Real.exp (p ^ 2) := by
  classical
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _a : α, Real.exp p := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun index _ => hm index)
    _ = Real.exp ((Fintype.card α : ℝ) * p) := by rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
    _ ≤ Real.exp (p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

theorem exists_finiteProductReconstruction_budget (C : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p → (p ^ 2 + p + 1 + C) ^ C ≤ (p + N) ^ N := by
  let P : Polynomial ℕ := (Polynomial.X ^ 2 + Polynomial.X + 1 + Polynomial.C C) ^ C
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  simpa [P, Polynomial.eval₂_add, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
