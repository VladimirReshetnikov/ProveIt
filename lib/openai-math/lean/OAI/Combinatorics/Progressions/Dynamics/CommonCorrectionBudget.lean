import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization

namespace OAI

section

namespace Erdos3

theorem exists_common_correction_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + (s + 2)) ^ (s + 2) * (p + 1) + (p + 2) ^ a + p + 2
      let t := ((q + 2) ^ 10 + 2) ^ 4
      separationBudget t + (t + 2) ^ 36 + ((t + 2) ^ 18 + t) ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) * (Polynomial.X + 1) +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let J : Polynomial ℕ := ((P + 2) ^ 10 + 2) ^ 4
  let B : Polynomial ℕ := (J + 2) ^ 48 + (J + 2) ^ 24 + J + 1 +
    (J + 2) ^ 36 + ((J + 2) ^ 18 + J)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, J, P, separationBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
