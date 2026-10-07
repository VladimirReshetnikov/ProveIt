import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

def fullInitialParameter (s C : ℕ) (p : ℝ) : ℝ :=
  p + p * (s + 2) * (p + 1) ^ (s + 1) + (p + C) ^ C + 2

theorem fullInitialParameter_controls (s C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ fullInitialParameter s C p ∧
      p * (s + 2) * (p + 1) ^ (s + 1) ≤ fullInitialParameter s C p ∧
      (p + C) ^ C ≤ fullInitialParameter s C p := by
  have hdim : 0 ≤ p * (s + 2) * (p + 1) ^ (s + 1) := by positivity
  have hC : 0 ≤ (p + C) ^ C := by positivity
  unfold fullInitialParameter
  exact ⟨by linarith, by linarith, by linarith⟩

theorem exists_fullInitialParameter_budget (s c C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (fullInitialParameter s c p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := Polynomial.X + Polynomial.X * Polynomial.C (s + 2) *
    (Polynomial.X + 1) ^ (s + 1) + (Polynomial.X + Polynomial.C c) ^ c + 2
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  simpa [Q, fullInitialParameter, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

section

namespace Erdos3

def commonTerminalParameter (s c : ℕ) (p : ℝ) : ℝ := fullInitialParameter s c p + (s + 1)

theorem commonTerminalParameter_controls (s c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ commonTerminalParameter s c p ∧
      p * (s + 2) * (p + 1) ^ (s + 1) ≤ commonTerminalParameter s c p ∧
      (p + c) ^ c ≤ commonTerminalParameter s c p ∧
      (s + 1 : ℕ) ≤ commonTerminalParameter s c p := by
  have h := fullInitialParameter_controls s c hp
  have hle : fullInitialParameter s c p ≤ commonTerminalParameter s c p :=
    le_add_of_nonneg_right (by positivity)
  refine ⟨h.1.trans hle, h.2.1.trans hle, h.2.2.trans hle, ?_⟩
  have hnonneg : 0 ≤ fullInitialParameter s c p := hp.trans h.1
  simpa only [commonTerminalParameter, Nat.cast_add, Nat.cast_one] using
    (le_add_of_nonneg_left hnonneg : ((s : ℝ) + 1) ≤ fullInitialParameter s c p + ((s : ℝ) + 1))

theorem exists_commonTerminalParameter_budget (s c C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      commonTerminalParameter s c p ≤ (p + D) ^ D ∧
      (commonTerminalParameter s c p + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := Polynomial.X + Polynomial.X * Polynomial.C (s + 2) *
    (Polynomial.X + 1) ^ (s + 1) + (Polynomial.X + Polynomial.C c) ^ c + 2 + Polynomial.C (s + 1)
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hq : 0 ≤ commonTerminalParameter s c p := hp.trans (commonTerminalParameter_controls s c hp).1
  have hpow : 0 ≤ (commonTerminalParameter s c p + C) ^ C := by positivity
  have hsum : commonTerminalParameter s c p + (commonTerminalParameter s c p + C) ^ C ≤ (p + D) ^ D := by
    simpa [Q, commonTerminalParameter, fullInitialParameter, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
