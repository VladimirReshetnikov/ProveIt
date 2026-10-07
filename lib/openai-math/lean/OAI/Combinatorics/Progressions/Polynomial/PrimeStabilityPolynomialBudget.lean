import OAI.Combinatorics.Progressions.Lattices.PrimeStabilityTree

namespace OAI

section

namespace Erdos3

universe u v w

theorem exists_prime_stability_polynomial_budget (s K Kf : ℕ) :
    ∃ L : ℕ, 2 ≤ L ∧ ∀ {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι]
      [Fintype σ] [DecidableEq σ] {bound : ℕ}
      (ctx : PrimeStabilityContext.{u, v, w} ι σ s bound) (Q : ℝ),
      0 ≤ Q → ctx.parameters.K ≤ K → ctx.parameters.Kf ≤ Kf →
      ctx.recordCap ≤ Q → ctx.primeBudget ≤ Q → (ctx.witnessSize : ℝ) ≤ Q →
      (ctx.mandatory.card : ℝ) ≤ Q → (bound : ℝ) ≤ Q →
      (ctx.allowance : ℝ) ≤ (Q + 2) ^ L ∧
      ctx.primeBudget * ctx.allowance + 5 * ctx.workBudget +
        2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16 ≤ (Q + 2) ^ L := by
  let U : Polynomial ℕ := (Polynomial.X + 2) ^ K
  let D : Polynomial ℕ := Polynomial.X +
    (2 * Polynomial.C s * U + 1 + Polynomial.X) * (Polynomial.X + 1) ^ s
  let P : Polynomial ℕ := D + Polynomial.X * D + 5 * U + 2 * (U + 2) ^ Kf + 16
  obtain ⟨L, hL, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨L, hL, ?_⟩
  intro ι σ _ _ _ _ bound ctx Q hQ hK hKf hb hp hr hM hd
  let ub : ℝ := (Q + 2) ^ K
  let db : ℝ := Q + (2 * s * ub + 1 + Q) * (Q + 1) ^ s
  have hub : 0 ≤ ub := by dsimp [ub]; positivity
  have hdb : 0 ≤ db := by dsimp [db]; positivity
  have hU0 := ctx.workBudget_nonneg
  have hU : ctx.workBudget ≤ ub := by
    calc
      ctx.workBudget ≤ (ctx.recordCap + 2) ^ ctx.parameters.K :=
        ctx.parameters.growth ctx.recordCap ctx.recordCap_nonneg
      _ ≤ (Q + 2) ^ ctx.parameters.K := pow_le_pow_left₀ (by linarith [ctx.recordCap_nonneg]) (by linarith) _
      _ ≤ (Q + 2) ^ K := pow_le_pow_right₀ (by linarith) hK
  have hperiod : (ctx.periodCap : ℝ) ≤ 2 * ((s : ℝ) * ctx.workBudget) + 1 := by
    exact (Nat.ceil_lt_add_one (show 0 ≤ 2 * ((s : ℝ) * ctx.workBudget) by positivity)).le
  have hcost : (ctx.stepCost : ℝ) ≤ 2 * s * ub + 1 + Q := by
    simp only [PrimeStabilityContext.stepCost, Nat.cast_add]
    have hmul := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2 * (s : ℝ) by positivity)
    nlinarith
  have hD : (ctx.allowance : ℝ) ≤ db := by
    simp only [PrimeStabilityContext.allowance, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
    dsimp only [db]
    gcongr
  have hF : (ctx.workBudget + 2) ^ ctx.parameters.Kf ≤ (ub + 2) ^ Kf :=
    (pow_le_pow_left₀ (by linarith) (show ctx.workBudget + 2 ≤ ub + 2 by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hKf)
  have hsum : db + Q * db + 5 * ub + 2 * (ub + 2) ^ Kf + 16 ≤ (Q + 2) ^ L := by
    simpa [P, D, U, ub, db, Polynomial.eval₂_pow] using hbudget Q hQ
  have hproduct : 0 ≤ Q * db := mul_nonneg hQ hdb
  have hpow : 0 ≤ (ub + 2) ^ Kf := by positivity
  refine ⟨hD.trans (by linarith), ?_⟩
  have hwidth : ctx.primeBudget * ctx.allowance + 5 * ctx.workBudget +
      2 * (ctx.workBudget + 2) ^ ctx.parameters.Kf + 16 ≤ Q * db + 5 * ub + 2 * (ub + 2) ^ Kf + 16 := by
    gcongr
  exact hwidth.trans (by linarith)

end Erdos3

end

end OAI
