import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_translationMajorDecomposition_budget (d a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let P := (p + a) ^ a
      let B := P + (P + c) ^ c + (2 * p + 2) ^ d + 1
      P ≤ (p + C) ^ C ∧
        (P + 2) ^ 4 ≤ (p + C) ^ C ∧
        (((d + 1 : ℕ) : ℝ) ^ 2 + 3) * (B + 2) ≤ (p + C) ^ C ∧
        2 * (((d + 1 : ℕ) : ℝ) ^ 2 + 1) * B ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let B : Polynomial ℕ := P + (P + Polynomial.C c) ^ c +
    (2 * Polynomial.X + 2) ^ d + 1
  let Q : Polynomial ℕ := (P + 2) ^ 4
  let R : Polynomial ℕ := Polynomial.C ((d + 1) ^ 2 + 3) * (B + 2)
  let S : Polynomial ℕ := Polynomial.C (2 * ((d + 1) ^ 2 + 1)) * B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Q + R + S)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hbound := hbudget p hp
  have hP := natPolynomial_eval_nonneg P hp
  have hQ := natPolynomial_eval_nonneg Q hp
  have hR := natPolynomial_eval_nonneg R hp
  have hS := natPolynomial_eval_nonneg S hp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_add] at hbound
  have hparts : P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      Q.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      R.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      S.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C :=
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  simpa only [P, B, Q, R, S, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one, Nat.coe_castRingHom,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hparts

end Erdos3

end

end OAI
