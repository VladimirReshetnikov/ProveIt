import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

def reducedRelativeParameter (s : ℕ) (p : ℝ) : ℝ :=
  2 * p + 2 * (p + (s + 2)) ^ (s + 2) + 4

theorem reducedRelativeParameter_controls (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reducedRelativeParameter s p ∧ p ≤ reducedRelativeParameter s p ∧
      2 * p ≤ reducedRelativeParameter s p ∧
      p + 2 * (p + (s + 2)) ^ (s + 2) + 2 ≤ reducedRelativeParameter s p + 2 := by
  have hd : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  unfold reducedRelativeParameter
  exact ⟨by positivity, by linarith, by linarith, by linarith⟩

theorem exists_reducedRelative_budget (s a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      4 * (p + (s + 2)) ^ (s + 2) + 2 + (reducedRelativeParameter s p + a) ^ a ≤
        (p + C) ^ C ∧
      (reducedRelativeParameter s p + b) ^ b ≤ (p + C) ^ C := by
  let D : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let Q : Polynomial ℕ := 2 * Polynomial.X + 2 * D + 4
  let P : Polynomial ℕ := 4 * D + 2 + (Q + Polynomial.C a) ^ a + (Q + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hd : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  have hq := (reducedRelativeParameter_controls s hp).1
  have ha : 0 ≤ (reducedRelativeParameter s p + a) ^ a := by positivity
  have hb : 0 ≤ (reducedRelativeParameter s p + b) ^ b := by positivity
  have hsum : 4 * (p + (s + 2)) ^ (s + 2) + 2 + (reducedRelativeParameter s p + a) ^ a +
      (reducedRelativeParameter s p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, D, reducedRelativeParameter, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
