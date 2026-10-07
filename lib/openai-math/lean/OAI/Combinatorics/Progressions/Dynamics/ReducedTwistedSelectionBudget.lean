import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

namespace Erdos3

theorem exists_reducedTwistedSelectionBudget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (raisedNiltestBudget ((p + a) ^ a) + c) ^ c ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let R : Polynomial ℕ := Q + (Q + 2) ^ 2 + 3
  let P : Polynomial ℕ := (R + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, R, Q, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp

theorem le_reducedTwistedInputBudget {a : ℕ} (ha : 2 ≤ a)
    {p : ℝ} (hp : 0 ≤ p) : p ≤ (p + a) ^ a := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbase : 1 ≤ p + a := by linarith
  calc
    p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
    _ = (p + a) ^ 1 := (pow_one _).symm
    _ ≤ (p + a) ^ a := pow_le_pow_right₀ hbase (by omega)

end Erdos3

end

end OAI
