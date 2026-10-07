import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

namespace Erdos3

def fixedListWorkingBudget (p b : ℝ) : ℝ := 10 * (p + b + 2)

theorem fixedListWorkingBudget_lower {p b : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) :
    2 ≤ fixedListWorkingBudget p b ∧ p ≤ fixedListWorkingBudget p b := by
  unfold fixedListWorkingBudget
  constructor <;> linarith

def fixedListComparisonBudget (B c : ℕ) (p : ℝ) : ℝ :=
  (fixedListWorkingBudget p ((p + 2) ^ B) + 2) ^ c

def fixedListRequiredBudget (B c : ℕ) (p : ℝ) : ℝ :=
  fixedListComparisonBudget B c p +
    productNiltestBudget (raisedNiltestBudget (fixedListComparisonBudget B c p))

noncomputable def fixedListBudgetPolynomial (B c : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  let q := Polynomial.C 10 * (X + (X + 2) ^ B + 2)
  let R := (q + 2) ^ c
  let S := R + (R + 2) ^ 2 + 3
  R + ((S + 2) ^ 2 + S + (S + (S ^ 2 + S + 3) ^ 2) + S ^ 2 + 4)

theorem fixedListBudgetPolynomial_eval (B c : ℕ) (p : ℝ) :
    (fixedListBudgetPolynomial B c).eval₂ (Nat.castRingHom ℝ) p =
      fixedListRequiredBudget B c p := by
  simp [fixedListBudgetPolynomial, fixedListRequiredBudget, fixedListComparisonBudget,
    fixedListWorkingBudget, productNiltestBudget, productObservableLipBudget,
    raisedNiltestBudget, Polynomial.eval₂_pow]

theorem exists_fixedListBudget_power (B c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      fixedListComparisonBudget B c p ≤ (p + 2) ^ C ∧
      productNiltestBudget (raisedNiltestBudget (fixedListComparisonBudget B c p)) ≤
        (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (fixedListBudgetPolynomial B c)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hsum : fixedListRequiredBudget B c p ≤ (p + 2) ^ C := by
    simpa only [fixedListBudgetPolynomial_eval] using hbound p hp
  have hR : 0 ≤ fixedListComparisonBudget B c p := by
    unfold fixedListComparisonBudget fixedListWorkingBudget
    positivity
  have hprod : 0 ≤ productNiltestBudget (raisedNiltestBudget (fixedListComparisonBudget B c p)) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  unfold fixedListRequiredBudget at hsum
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
