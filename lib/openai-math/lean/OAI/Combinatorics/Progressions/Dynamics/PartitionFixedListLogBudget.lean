import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

theorem partition_pair_log_bound {F Q : ℝ} (hF : 0 ≤ F) (hQ : 0 ≤ Q)
    (hcard : F ≤ Real.exp Q) : Real.log (F + F ^ 2 + 2) ≤ 2 * Q + 4 := by
  have h1 : 1 ≤ Real.exp Q := Real.one_le_exp hQ
  have hE : Real.exp Q ≤ Real.exp Q ^ 2 := by nlinarith
  have hF2 : F ^ 2 ≤ Real.exp Q ^ 2 := pow_le_pow_left₀ hF hcard 2
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hsum : F + F ^ 2 + 2 ≤ Real.exp (2 * Q + 4) := by
    calc
      _ ≤ 4 * Real.exp Q ^ 2 := by nlinarith
      _ ≤ Real.exp 4 * Real.exp Q ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      _ = Real.exp (2 * Q + 4) := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  exact (Real.log_le_iff_le_exp (by positivity)).mpr hsum

theorem log_reciprocal_of_exp_lower {R δ : ℝ} (hδ : Real.exp (-R) ≤ δ) :
    Real.log (1 / δ) ≤ R := by
  have hh := Real.log_le_log (Real.exp_pos (-R)) hδ
  rw [Real.log_exp] at hh
  rw [one_div, Real.log_inv]
  linarith

theorem exists_partition_fixed_list_log_budget (C k : ℕ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ p : ℝ, 0 ≤ p →
      3 * ((p + C) ^ C + 2) + 4 + 2 * (p + 2) ^ k ≤ (p + 2) ^ b := by
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨b, hb, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (3 * ((X + Polynomial.C C) ^ C + 2) + 4 + 2 * (X + 2) ^ k)
  refine ⟨b, hb, ?_⟩
  intro p hp
  simpa [X, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
