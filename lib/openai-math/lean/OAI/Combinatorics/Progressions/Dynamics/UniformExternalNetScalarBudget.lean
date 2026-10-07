import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_uniformExternalNetScalarBudget (netExponent localExponent : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p ε : ℝ, 0 ≤ p → 0 < ε → ε ≤ 1 →
      ∃ q : ℝ, 0 ≤ q ∧ p ≤ q ∧ Real.log (1 / ε) ≤ q ∧
        (p + Real.log (1 / (ε / 3)) + netExponent) ^ netExponent ≤ q ∧
        (q + localExponent) ^ localExponent ≤ (p + Real.log (1 / ε) + C) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C netExponent + 3) ^ netExponent +
      3 + Polynomial.C localExponent) ^ localExponent
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p ε hp hε hε1
  have hlog : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div hε).2 hε1)
  have hlogThree : Real.log (1 / (ε / 3)) = Real.log (1 / ε) + Real.log 3 := by
    rw [show (1 : ℝ) / (ε / 3) = (1 / ε) * 3 by field_simp]
    exact Real.log_mul (by positivity) (by norm_num)
  have hthree : Real.log (3 : ℝ) ≤ 3 := Real.log_le_self (by norm_num)
  have hthree0 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  let x := p + Real.log (1 / ε)
  have hx : 0 ≤ x := add_nonneg hp hlog
  let q := x + (x + netExponent + 3) ^ netExponent + 3
  have hpower : 0 ≤ (x + netExponent + 3) ^ netExponent := by positivity
  refine ⟨q, by dsimp [q]; positivity, ?_, ?_, ?_, ?_⟩
  · dsimp [q, x]
    linarith only [hlog, hpower]
  · dsimp [q, x]
    linarith only [hp, hpower]
  · have hbase0 : 0 ≤ p + Real.log (1 / (ε / 3)) + netExponent := by
      rw [hlogThree]
      positivity
    have hbase : p + Real.log (1 / (ε / 3)) + netExponent ≤
        x + netExponent + 3 := by
      rw [hlogThree]
      dsimp [x]
      linarith only [hthree]
    exact (pow_le_pow_left₀ hbase0 hbase netExponent).trans (by dsimp [q]; linarith)
  · simpa [P, q, x, Polynomial.eval₂_pow] using hbudget x hx

end Erdos3

end

end OAI
