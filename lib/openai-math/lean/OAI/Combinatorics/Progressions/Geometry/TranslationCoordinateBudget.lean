import OAI.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_translationCoordinate_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n t q : ℕ) (p M B : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (t : ℝ) ≤ Real.exp p →
      0 ≤ M → M ≤ Real.exp p → 0 ≤ B → B ≤ Real.exp p →
      (q : ℝ) ≤ Real.exp p →
      ((d : ℝ) + 1) * ((t : ℝ) * M * B) *
          (1 + (n : ℝ) * d * ((t : ℝ) * M * B)) ^ d ≤
        Real.exp ((p + C) ^ C) ∧
      (d.factorial * q ^ (d + 1) : ℕ) ≤ Real.exp ((p + C) ^ C) := by
  let Q : Polynomial ℕ :=
    Polynomial.C (5 * d + 4) * Polynomial.X +
      Polynomial.C (d ^ 2 + 2 * d + 1 + d.factorial)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro n t q p M B hp hn ht hM hMp hB hBp hq
  have htotal : (5 * (d : ℝ) + 4) * p +
      ((d : ℝ) ^ 2 + 2 * d + 1 + d.factorial) ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using hbudget p hp
  have hmasscost : (4 * (d : ℝ) + 3) * p + d ^ 2 + 2 * d + 1 ≤
      (p + C) ^ C := by
    have h := mul_nonneg ((show (0 : ℝ) ≤ d + 1 by positivity)) hp
    have hf : (0 : ℝ) ≤ d.factorial := Nat.cast_nonneg _
    nlinarith
  have hdenomcost : (d.factorial : ℝ) + ((d : ℝ) + 1) * p ≤ (p + C) ^ C := by
    have h := mul_nonneg ((show (0 : ℝ) ≤ 4 * d + 3 by positivity)) hp
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith [sq_nonneg (d : ℝ)]
  have hnp : (n : ℝ) ≤ Real.exp p := hn.trans (by linarith [Real.add_one_le_exp p])
  have hdp : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have ha : (t : ℝ) * M * B ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hprod : (n : ℝ) * d * ((t : ℝ) * M * B) ≤ Real.exp (4 * p + d) := by
    calc
      _ ≤ Real.exp p * Real.exp d * Real.exp (3 * p) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hplus : 1 + (n : ℝ) * d * ((t : ℝ) * M * B) ≤
      Real.exp (4 * p + d + 1) := one_add_le_exp_succ (by positivity) hprod
  have hfactor : (d : ℝ) + 1 ≤ Real.exp ((d : ℝ) + 1) := by
    linarith [Real.add_one_le_exp ((d : ℝ) + 1)]
  constructor
  · calc
      _ ≤ Real.exp ((d : ℝ) + 1) * Real.exp (3 * p) *
          Real.exp (4 * p + d + 1) ^ d := by gcongr
      _ = Real.exp ((4 * (d : ℝ) + 3) * p + d ^ 2 + 2 * d + 1) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hmasscost
  · have hf : (d.factorial : ℝ) ≤ Real.exp d.factorial := by
      linarith [Real.add_one_le_exp (d.factorial : ℝ)]
    push_cast
    calc
      (d.factorial : ℝ) * (q : ℝ) ^ (d + 1) ≤
          Real.exp d.factorial * (Real.exp p) ^ (d + 1) := by gcongr
      _ = Real.exp ((d.factorial : ℝ) + ((d : ℝ) + 1) * p) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        rfl
      _ ≤ _ := Real.exp_le_exp.mpr hdenomcost

end Erdos3

end

end OAI
