import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight
import OAI.Combinatorics.Progressions.Estimates.SquarefreeStructureHeight
import OAI.Combinatorics.Progressions.Sampling.IntegralGridBudget

namespace OAI

section

namespace Erdos3

theorem squarefreeBracketHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (squarefreeBracketHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hcube : ((H * H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p := by
        push_cast
        gcongr
      _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hsq : ((n ^ 2 : ℕ) : ℝ) ≤ (p + 2) ^ 2 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (hn.trans (by linarith)) 2
  exact rational_sum_cost_le_exp (n ^ 2) (H * H * H) hp 2 2 hcube hsq

theorem squarefreeStructureHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (squarefreeStructureHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 8) := by
  have hprod : ((rationalSolveHeight n H * squarefreeBracketHeight n H : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 6) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 5) * Real.exp ((p + 2) ^ 5) :=
        mul_le_mul (rationalSolveHeight_le_budget n H hp hn hH)
          (squarefreeBracketHeight_le_exp n H hp hn hH) (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * (p + 2) ^ 5) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (p + 2) * (p + 2) ^ 5 := by gcongr; linarith
          _ = _ := by ring
  exact rational_sum_cost_le_exp n _ hp 6 1 hprod (by simpa only [pow_one] using hn.trans (by linarith))

end Erdos3

end

section

namespace Erdos3

noncomputable def squarefreeInputBudget (t : ℕ) (p : ℝ) : ℝ := (2 : ℝ) ^ t * p + (p + 3) ^ 8

noncomputable def squarefreeModelBudget (t : ℕ) (p : ℝ) : ℝ :=
  squarefreeInputBudget t p +
    (squarefreeInputBudget t p + (bchIntegralDenominatorBound t + 5 : ℕ)) ^
      (bchIntegralDenominatorBound t + 5)

theorem squarefreeInputBudget_nonneg (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ squarefreeInputBudget t p := by
  unfold squarefreeInputBudget
  positivity

theorem le_squarefreeInputBudget (t : ℕ) {p : ℝ} (hp : 0 ≤ p) : p ≤ squarefreeInputBudget t p := by
  have hp2 : p ≤ (2 : ℝ) ^ t * p := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hp
  exact hp2.trans (le_add_of_nonneg_right (by positivity))

theorem squarefreeInputBudget_le_model (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeInputBudget t p ≤ squarefreeModelBudget t p := by
  have hq := squarefreeInputBudget_nonneg t hp
  exact le_add_of_nonneg_right (pow_nonneg (add_nonneg hq (Nat.cast_nonneg _)) _)

theorem squarefreeStructureHeight_ceil_exp (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) :
    (squarefreeStructureHeight n ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 8) := by
  have h := squarefreeStructureHeight_le_exp n ⌈Real.exp p⌉₊
    (p := p + 1) (by linarith) (by linarith) (ceil_exp_le_exp_add_one hp)
  have heq : p + 1 + 2 = p + 3 := by ring
  simpa only [heq] using h

theorem squarefree_grid_budget (t N d l B : ℕ) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hN : N ≤ 2 ^ t * d) (hl : (l : ℝ) ≤ Real.exp p)
    (hB : B ≤ bchIntegralDenominatorBound t *
      squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (N ^ 3) * l) :
    (B : ℝ) ≤ Real.exp (squarefreeModelBudget t p) := by
  have hq := squarefreeInputBudget_nonneg t hp
  have hpq := le_squarefreeInputBudget t hp
  have hNq : (N : ℝ) ≤ squarefreeInputBudget t p := by
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (squarefreeInputBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hd).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (mul_nonneg (by positivity) hp)))
  exact (Nat.cast_le.mpr hB).trans ((integral_grid_allowance_le_exp
    (bchIntegralDenominatorBound t) N _ l hq hNq hHq
    (hl.trans (Real.exp_le_exp.mpr hpq))).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left hq)))

end Erdos3

end

end OAI
