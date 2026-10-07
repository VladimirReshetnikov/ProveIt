import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.Combinatorics.Progressions.Estimates.RationalRowReduction

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem factorial_le_exp_sq (r : ℕ) :
    (r.factorial : ℝ) ≤ Real.exp ((r : ℝ) ^ 2) := by
  calc
    (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
    _ ≤ (Real.exp r) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _)
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp r)) r
    _ = Real.exp ((r : ℝ) ^ 2) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem rationalSolveHeight_le_exp (r H : ℕ) {p : ℝ} (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalSolveHeight r H : ℝ) ≤
      Real.exp ((r : ℝ) ^ 2 + p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2)) := by
  have hpower : (((H : ℝ) ^ (r * r + r)) ^ r) ≤
      Real.exp (p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2)) := by
    calc
      _ ≤ ((Real.exp p) ^ (r * r + r)) ^ r := by gcongr
      _ = _ := by rw [← pow_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  unfold rationalSolveHeight
  push_cast
  calc
    _ ≤ Real.exp ((r : ℝ) ^ 2) *
        Real.exp (p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2)) :=
      mul_le_mul (factorial_le_exp_sq r) hpower (by positivity) (by positivity)
    _ = _ := (Real.exp_add _ _).symm

theorem rationalSolveHeight_le_budget (r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalSolveHeight r H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  apply (rationalSolveHeight_le_exp r H hH).trans
  apply Real.exp_le_exp.mpr
  calc
    (r : ℝ) ^ 2 + p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2) ≤
        p ^ 2 + p * (p ^ 3 + p ^ 2) := by gcongr
    _ ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 9 * p ^ 4 + 39 * p ^ 3 + 79 * p ^ 2 + 80 * p + 32 := by
        positivity
      nlinarith

theorem exists_rational_section_exp_height {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℚ) (hsurj : Function.Surjective A.mulVec)
    {H : ℕ} (hHpos : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ S : Matrix κ ι ℚ, A * S = 1 ∧ ∀ i j,
      ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 5) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section A hsurj hHpos hA
  refine ⟨S, hS, fun i j => ?_⟩
  have hbudget := rationalSolveHeight_le_budget (Fintype.card ι) H hp hdim hH
  constructor
  · exact (show ((S i j).num.natAbs : ℝ) ≤ rationalSolveHeight (Fintype.card ι) H from
      by exact_mod_cast (hSH i j).1).trans hbudget
  · exact (show ((S i j).den : ℝ) ≤ rationalSolveHeight (Fintype.card ι) H from
      by exact_mod_cast (hSH i j).2).trans hbudget

end Erdos3

end

end OAI
