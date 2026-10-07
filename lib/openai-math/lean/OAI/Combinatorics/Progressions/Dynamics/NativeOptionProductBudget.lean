import OAI.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped NNReal

theorem exists_optionProductMetric_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (d : Option ι → ℕ) {p : ℝ},
      0 ≤ p → (Fintype.card (Option ι) : ℝ) ≤ p → (∀ i, (d i : ℝ) ≤ p) →
      (((1 + productMetricBound (fun i => d (some i))) * productMetricBound d : ℝ≥0) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let T := 2 * X * (X ^ 2 + X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((1 + T) * T)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ d p hp hι hd
  have hι' : (Fintype.card ι : ℝ) ≤ p := by
    simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one] at hι
    linarith
  have hfull := productMetricBound_le d hp hι hd
  have hrest := productMetricBound_le (fun i => d (some i)) hp hι' (fun i => hd (some i))
  have hpoly : (1 + 2 * p * (p ^ 2 + p + 1)) * (2 * p * (p ^ 2 + p + 1)) ≤
      (p + C) ^ C := by
    simpa [T, X, Polynomial.eval₂_pow] using hbudget p hp
  calc
    _ ≤ (1 + 2 * p * (p ^ 2 + p + 1)) * (2 * p * (p ^ 2 + p + 1)) := by
      push_cast
      gcongr
    _ ≤ (p + C) ^ C := hpoly
    _ ≤ Real.exp ((p + C) ^ C) := by linarith [Real.add_one_le_exp ((p + C) ^ C)]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
