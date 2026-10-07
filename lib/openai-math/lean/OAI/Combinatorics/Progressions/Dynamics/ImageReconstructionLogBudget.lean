import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

def imageRepresentativeLogBudget (C : ℕ) (p : ℝ) : ℝ :=
  ((p + 2) ^ 4 + C) ^ C + (p + 2) ^ 2

def generalReconstructionLogBudget (C D E F Z : ℕ) (p : ℝ) : ℝ :=
  let q := p + imageRepresentativeLogBudget C p + 1
  p + (p + 2) ^ 18 + (p + 2) ^ 48 + (p + 2) ^ 24 +
    ((p + Z) ^ Z + 1) + (q + D + E) ^ E + (q + F) ^ F + 1

theorem generalReconstructionLogBudget_bounds (C D E F Z : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let q := p + imageRepresentativeLogBudget C p + 1
    let r := generalReconstructionLogBudget C D E F Z p
    1 ≤ r ∧ p ≤ r ∧ (p + 2) ^ 18 ≤ r ∧ (p + 2) ^ 48 ≤ r ∧ (p + 2) ^ 24 ≤ r ∧
      (p + Z) ^ Z + 1 ≤ r ∧ (q + D + E) ^ E ≤ r ∧ (q + F) ^ F ≤ r := by
  have hq : 0 ≤ p + imageRepresentativeLogBudget C p + 1 := by
    dsimp [imageRepresentativeLogBudget]
    positivity
  have h18 : 0 ≤ (p + 2) ^ 18 := by positivity
  have h48 : 0 ≤ (p + 2) ^ 48 := by positivity
  have h24 : 0 ≤ (p + 2) ^ 24 := by positivity
  have hZ : 0 ≤ (p + Z) ^ Z + 1 := by positivity
  have hE : 0 ≤ (p + imageRepresentativeLogBudget C p + 1 + D + E) ^ E := by positivity
  have hF : 0 ≤ (p + imageRepresentativeLogBudget C p + 1 + F) ^ F := by positivity
  dsimp only [generalReconstructionLogBudget]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem exists_generalReconstructionLogBudget_bound (C D E F Z : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      40 * generalReconstructionLogBudget C D E F Z p ≤ (p + N) ^ N := by
  let R : Polynomial ℕ := ((Polynomial.X + 2) ^ 4 + Polynomial.C C) ^ C + (Polynomial.X + 2) ^ 2
  let q : Polynomial ℕ := Polynomial.X + R + 1
  let P : Polynomial ℕ := 40 * (Polynomial.X + (Polynomial.X + 2) ^ 18 +
    (Polynomial.X + 2) ^ 48 + (Polynomial.X + 2) ^ 24 +
    ((Polynomial.X + Polynomial.C Z) ^ Z + 1) +
    (q + Polynomial.C D + Polynomial.C E) ^ E + (q + Polynomial.C F) ^ F + 1)
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  have heq : P.eval₂ (Nat.castRingHom ℝ) p = 40 * generalReconstructionLogBudget C D E F Z p := by
    simp [P, q, R, generalReconstructionLogBudget, imageRepresentativeLogBudget,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  rw [← heq]
  exact hbound p hp

end Erdos3

end

end OAI
