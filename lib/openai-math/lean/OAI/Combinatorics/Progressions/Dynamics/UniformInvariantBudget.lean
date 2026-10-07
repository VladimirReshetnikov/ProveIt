import OAI.Combinatorics.Progressions.Estimates.SourceUnitCover

namespace OAI

section

namespace Erdos3

theorem exists_uniform_invariantVertical_cost (M : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m : ℕ), m ≤ M → ∀ p : ℝ, 0 ≤ p →
      invariantVerticalBudget m p ≤ (p + C) ^ C := by
  let B := (Finset.range (M + 1)).sup symmetricUnitConstant
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C (2 * M + 2) * (2 * X + 1) + Polynomial.C B + X + Polynomial.C M + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro m hm p hp
  have hb : symmetricUnitConstant m ≤ B := Finset.le_sup (f := symmetricUnitConstant)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  have hmr : (m : ℝ) ≤ M := by exact_mod_cast hm
  have hbr : (symmetricUnitConstant m : ℝ) ≤ B := by exact_mod_cast hb
  have hle : invariantVerticalBudget m p ≤
      (2 * M + 2 : ℝ) * (2 * p + 1) + B + p + M + 1 := by
    dsimp [invariantVerticalBudget, symmetricUnitBudget]
    nlinarith
  apply hle.trans
  simpa [P, X] using hbound p hp

end Erdos3

end

end OAI
