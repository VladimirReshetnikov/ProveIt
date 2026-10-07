import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_translationMajorSeparated_budget (a c s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let p1 := (p + a) ^ a
      p1 ≤ (p + C) ^ C ∧
        (p1 + c) ^ c ≤ (p + C) ^ C ∧
        (p1 + s) ^ s ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := (P + Polynomial.C c) ^ c
  let R : Polynomial ℕ := (P + Polynomial.C s) ^ s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Q + R)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have htotal : (p + a) ^ a + ((p + a) ^ a + c) ^ c +
      ((p + a) ^ a + s) ^ s ≤ (p + C) ^ C := by
    simpa only [P, Q, R, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Nat.coe_castRingHom]
      using hbudget p hp
  have hP : 0 ≤ (p + a) ^ a := by positivity
  have hQ : 0 ≤ ((p + a) ^ a + c) ^ c := by positivity
  have hR : 0 ≤ ((p + a) ^ a + s) ^ s := by positivity
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
