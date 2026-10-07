import OAI.Combinatorics.Progressions.Estimates.AdaptedMarkedMapHeight

namespace OAI

section

namespace Erdos3

def markedRefilteredBasisInput (p : ℝ) : ℝ :=
  p + adaptedMarkedMapHeightBudget p + 1

def markedRefilteredMapInput (p : ℝ) : ℝ :=
  markedRefilteredBasisInput p + (markedRefilteredBasisInput p + 2) ^ 4

def markedRefilteredModelInput (A : ℕ) (p : ℝ) : ℝ :=
  p + markedRefilteredMapInput p + (markedRefilteredMapInput p + A) ^ A + 1

theorem markedRefilteredModelInput_bounds (A : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let q := markedRefilteredBasisInput p
    let t := markedRefilteredMapInput p
    let r := markedRefilteredModelInput A p
    0 ≤ q ∧ p ≤ q ∧ adaptedMarkedMapHeightBudget p ≤ q ∧
      0 ≤ t ∧ q ≤ t ∧ (q + 2) ^ 4 ≤ t ∧
      0 ≤ r ∧ p ≤ r ∧ (t + A) ^ A ≤ r := by
  dsimp only
  have hb : 0 ≤ adaptedMarkedMapHeightBudget p := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  have hq : 0 ≤ markedRefilteredBasisInput p := by
    unfold markedRefilteredBasisInput
    positivity
  have hpq : p ≤ markedRefilteredBasisInput p := by
    unfold markedRefilteredBasisInput
    linarith only [hb]
  have hbq : adaptedMarkedMapHeightBudget p ≤ markedRefilteredBasisInput p := by
    unfold markedRefilteredBasisInput
    linarith only [hp]
  have hpow : 0 ≤ (markedRefilteredBasisInput p + 2) ^ 4 := by positivity
  have ht : 0 ≤ markedRefilteredMapInput p := add_nonneg hq hpow
  have hqt : markedRefilteredBasisInput p ≤ markedRefilteredMapInput p :=
    le_add_of_nonneg_right hpow
  have hpowt : (markedRefilteredBasisInput p + 2) ^ 4 ≤ markedRefilteredMapInput p :=
    le_add_of_nonneg_left hq
  have hmodel : 0 ≤ (markedRefilteredMapInput p + A) ^ A := by positivity
  have hr : 0 ≤ markedRefilteredModelInput A p := by
    unfold markedRefilteredModelInput
    positivity
  have hpr : p ≤ markedRefilteredModelInput A p := by
    unfold markedRefilteredModelInput
    linarith only [ht, hmodel]
  have hmodelr : (markedRefilteredMapInput p + A) ^ A ≤ markedRefilteredModelInput A p := by
    unfold markedRefilteredModelInput
    linarith only [hp, ht]
  exact ⟨hq, hpq, hbq, ht, hqt, hpowt, hr, hpr, hmodelr⟩

theorem exists_markedRefilteredModelInput_budget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      markedRefilteredModelInput A p ≤ (p + C) ^ C ∧
      ((markedRefilteredModelInput A p + 2) ^ 4 + markedRefilteredModelInput A p + 4) ^ 8 ≤
        (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X +
    (Polynomial.X + (Polynomial.X + 4) ^ 5 + (Polynomial.X + 2) ^ 4 + 2) ^ 4 + 1
  let T : Polynomial ℕ := Q + (Q + 2) ^ 4
  let R : Polynomial ℕ := Polynomial.X + T + (T + Polynomial.C A) ^ A + 1
  let P : Polynomial ℕ := R + ((R + 2) ^ 4 + R + 4) ^ 8
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  have hr := (markedRefilteredModelInput_bounds A hp).2.2.2.2.2.2.1
  have hcost : 0 ≤
      ((markedRefilteredModelInput A p + 2) ^ 4 + markedRefilteredModelInput A p + 4) ^ 8 := by
    positivity
  have hsum : markedRefilteredModelInput A p +
      ((markedRefilteredModelInput A p + 2) ^ 4 + markedRefilteredModelInput A p + 4) ^ 8 ≤
      (p + C) ^ C := by
    simpa [P, R, T, Q, markedRefilteredModelInput, markedRefilteredMapInput,
      markedRefilteredBasisInput, adaptedMarkedMapHeightBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  exact ⟨(le_add_of_nonneg_right hcost).trans hsum, (le_add_of_nonneg_left hr).trans hsum⟩

end Erdos3

end

end OAI
