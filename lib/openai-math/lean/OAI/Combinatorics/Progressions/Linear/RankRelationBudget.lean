import OAI.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval

namespace OAI

section

namespace Erdos3

theorem exists_rank_relation_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let K := (p + a) ^ a
      let q := K + (K + c) ^ c + 2
      11 * q + 7 ≤ (p + C) ^ C ∧ mixedErrorPairBudget q ≤ (p + C) ^ C := by
  obtain ⟨b, _, hpair⟩ := exists_mixed_error_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  let Z := Y + (Y + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (11 * Z + 7 + (Z + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp K q
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hterm : 0 ≤ (q + b) ^ b := by positivity
  have hbound : 11 * q + 7 + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Y, Z, K, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hterm, hbound],
    (hpair q hq).1.trans (by linarith only [hq, hbound])⟩

end Erdos3

end

end OAI
