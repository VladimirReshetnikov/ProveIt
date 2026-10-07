import Mathlib.Data.Nat.Factorial.BigOperators
import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem multidegreeFactorial_mono {a b : σ → ℕ} (h : a ≤ b) :
    multidegreeFactorial a ≤ multidegreeFactorial b :=
  Finset.prod_le_prod (fun i _ => Nat.factorial_le (h i))

theorem multidegreeFactorial_le_total (a : σ → ℕ) :
    multidegreeFactorial a ≤ (∑ i, a i).factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ a)

noncomputable def comparisonBasisHeight (bound : σ → ℕ) (p : ℝ) : ℕ :=
  ⌈Real.exp p⌉₊ * multidegreeFactorial bound

def comparisonBasisBudget (t : ℕ) (p : ℝ) : ℝ := p + 1 + (t : ℝ) ^ 2

theorem comparisonBasisHeight_ge_ceil (bound : σ → ℕ) (p : ℝ) :
    ⌈Real.exp p⌉₊ ≤ comparisonBasisHeight bound p :=
  Nat.le_mul_of_pos_right _ (multidegreeFactorial_pos bound)

theorem comparisonBasisHeight_ge_factorial (bound : σ → ℕ) (p : ℝ) :
    multidegreeFactorial bound ≤ comparisonBasisHeight bound p :=
  Nat.le_mul_of_pos_left _ (one_le_ceil_exp p)

theorem comparisonBasisHeight_pos (bound : σ → ℕ) (p : ℝ) :
    0 < comparisonBasisHeight bound p :=
  (multidegreeFactorial_pos bound).trans_le (comparisonBasisHeight_ge_factorial bound p)

theorem comparisonBasisHeight_le_exp (bound : σ → ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (comparisonBasisHeight bound p : ℝ) ≤ Real.exp (comparisonBasisBudget (∑ i, bound i) p) := by
  have hf : (multidegreeFactorial bound : ℝ) ≤ Real.exp (((∑ i, bound i : ℕ) : ℝ) ^ 2) := by
    exact (Nat.cast_le.mpr (multidegreeFactorial_le_total bound)).trans (factorial_le_exp_sq _)
  rw [comparisonBasisHeight, Nat.cast_mul]
  calc
    _ ≤ Real.exp (p + 1) * Real.exp (((∑ i, bound i : ℕ) : ℝ) ^ 2) :=
      mul_le_mul (ceil_exp_le_exp_add_one hp) hf (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

end OAI
