import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_translationMajor_detected_potential_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + a) ^ a
      (q + (q + 2)^4 + 1 + c)^c ≤ (p + C)^C ∧ q ≤ (p + C)^C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a)^a
  let R : Polynomial ℕ := (Q + (Q + 2)^4 + 1 + Polynomial.C c)^c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (Q + R)
  refine ⟨C, hC, fun p hp => ?_⟩
  let q : ℝ := (p + a)^a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hR : 0 ≤ (q + (q + 2)^4 + 1 + c)^c := by positivity
  have hsum : q + (q + (q + 2)^4 + 1 + c)^c ≤ (p + C)^C := by
    simpa [Q, R, q, Polynomial.eval₂_pow] using hbound p hp
  exact ⟨(le_add_of_nonneg_left hq).trans hsum, (le_add_of_nonneg_right hR).trans hsum⟩

theorem translationMajor_initial_budget_bounds (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ (p + a)^a ∧ p ≤ (p + a)^a ∧ 1 ≤ (p + a)^a := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbase : (1 : ℝ) ≤ p + a := by linarith
  have hpow : p + a ≤ (p + a)^a := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ a by omega)
  exact ⟨(zero_le_one.trans hbase).trans hpow,
    (le_add_of_nonneg_right (Nat.cast_nonneg a)).trans hpow, hbase.trans hpow⟩

end Erdos3

end

end OAI
