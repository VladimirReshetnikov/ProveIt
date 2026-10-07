import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

def doublePowerParameter (a b : ℕ) (p : ℝ) : ℝ := p + (3 * p + 2) ^ a + (p + 2) ^ b + 2

theorem doublePowerParameter_controls (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ doublePowerParameter a b p ∧ (3 * p + 2) ^ a ≤ doublePowerParameter a b p ∧
      (p + 2) ^ b ≤ doublePowerParameter a b p := by
  have h₁ : 0 ≤ (3 * p + 2) ^ a := by positivity
  have h₂ : 0 ≤ (p + 2) ^ b := by positivity
  have hlast : p + (3 * p + 2) ^ a + (p + 2) ^ b ≤ doublePowerParameter a b p :=
    le_add_of_nonneg_right (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · exact ((le_add_of_nonneg_right h₁).trans (le_add_of_nonneg_right h₂)).trans hlast
  · exact ((le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right h₂)).trans hlast
  · exact (le_add_of_nonneg_left (add_nonneg hp h₁)).trans hlast

theorem exists_doublePowerParameter_budget (a b C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (doublePowerParameter a b p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := Polynomial.X + (3 * Polynomial.X + 2) ^ a + (Polynomial.X + 2) ^ b + 2
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  simpa [Q, doublePowerParameter, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

section

namespace Erdos3

def fastTerminalParameter (p : ℝ) : ℝ := doublePowerParameter 294 7 p

theorem fastTerminalParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ fastTerminalParameter p ∧ (3 * p + 2) ^ 294 ≤ fastTerminalParameter p ∧
      (p + 2) ^ 7 ≤ fastTerminalParameter p :=
  doublePowerParameter_controls 294 7 hp

theorem exists_fastTerminalParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (fastTerminalParameter p + C) ^ C ≤ (p + D) ^ D :=
  exists_doublePowerParameter_budget 294 7 C

end Erdos3

end

end OAI
