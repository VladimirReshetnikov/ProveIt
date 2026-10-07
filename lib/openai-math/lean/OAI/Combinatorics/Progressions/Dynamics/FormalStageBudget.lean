import OAI.Combinatorics.Progressions.Nilpotent.BracketStepBudget
import OAI.Combinatorics.Progressions.Nilpotent.ControlledBracketToCurrentLayer

namespace OAI

section

namespace Erdos3

theorem bracketTransitionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ bracketTransitionBudget p := by unfold bracketTransitionBudget; positivity

theorem le_bracketTransitionBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ bracketTransitionBudget p := by
  have h8 : 0 ≤ (p + 2) ^ 8 := by positivity
  have h9 : 0 ≤ (p + 2) ^ 9 := by positivity
  unfold bracketTransitionBudget
  linarith

theorem exists_formal_stage_budget (D E : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let d := (p + D) ^ D
      let u := bracketTransitionBudget (p + d)
      let q := u + bracketConstructionBudget u
      d + (q + E) ^ E + 1 ≤ (p + C) ^ C := by
  let Pd : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D
  let Pt : Polynomial ℕ := Polynomial.X + Pd
  let Pu : Polynomial ℕ := 4 * Pt + (Pt + 2) ^ 8 + (Pt + 2) ^ 9 + 1
  let Pq : Polynomial ℕ := Pu + ((Pu + 2) ^ 3 + 3 * Pu + 2)
  let P : Polynomial ℕ := Pd + (Pq + Polynomial.C E) ^ E + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Pd, Pt, Pu, Pq, bracketTransitionBudget, bracketConstructionBudget,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
