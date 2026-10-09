import OAI.Combinatorics.Progressions.Polynomial.WeylStepScales

/-! Numerical bounds for the Weyl budget constants of degrees one to three.

`Proofs05ExplicitSchmidtRecurrence` names the Schmidt recurrence constants
through `A_j = (weylBudgetPolynomial j).eval 1` and
`d_j = natDegree (weylBudgetPolynomial j) + 1`. A budget comparison needs
upper bounds on them; these are crude but explicit:
* `weylBudgetPolynomial_eval_one_lt`: `A_j < 2^192` for `j ≤ 2`;
* `weylBudgetPolynomial_natDegree_lt`: `natDegree < 256` for `j ≤ 2`.

The degree bound avoids degree bookkeeping through `comp` and `pow`: a nonzero
polynomial over `ℕ` has `2^natDegree ≤ P(2)` (`two_pow_natDegree_le_eval_two`),
and `P(2) = weylBudget j 2` is a computable natural number. This module imports
only `WeylStepScales` from the port, so it is checked locally. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

open Polynomial

/-- A nonzero natural polynomial is at least `2^natDegree` at `2`. -/
theorem two_pow_natDegree_le_eval_two (P : Polynomial ℕ) (hP : P ≠ 0) :
    2 ^ P.natDegree ≤ P.eval 2 := by
  rw [eval_eq_sum_range]
  have hlc : 1 ≤ P.coeff P.natDegree :=
    Nat.one_le_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
  calc 2 ^ P.natDegree ≤ P.coeff P.natDegree * 2 ^ P.natDegree := Nat.le_mul_of_pos_left _ hlc
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * 2 ^ i :=
      Finset.single_le_sum (f := fun i => P.coeff i * 2 ^ i) (fun _ _ => Nat.zero_le _)
        (Finset.self_mem_range_succ _)

theorem weylBudget_one_lt (j : Nat) (hj : j ≤ 2) : OAI.Erdos3.weylBudget j 1 < 2 ^ 192 := by
  interval_cases j <;>
    simp only [OAI.Erdos3.weylBudget, OAI.Erdos3.weylNextBudget] <;> norm_num

theorem weylBudget_two_lt (j : Nat) (hj : j ≤ 2) :
    OAI.Erdos3.weylBudget j 2 < 2 ^ 128 * 2 ^ 128 := by
  interval_cases j <;>
    simp only [OAI.Erdos3.weylBudget, OAI.Erdos3.weylNextBudget] <;> norm_num

/-- **The Weyl coefficient sum is below `2^192` in degrees one to three.** -/
theorem weylBudgetPolynomial_eval_one_lt (j : Nat) (hj : j ≤ 2) :
    (OAI.Erdos3.weylBudgetPolynomial j).eval 1 < 2 ^ 192 := by
  rw [OAI.Erdos3.weylBudgetPolynomial_eval]
  exact weylBudget_one_lt j hj

/-- **The Weyl budget polynomial has degree below `256` in degrees one to three.** -/
theorem weylBudgetPolynomial_natDegree_lt (j : Nat) (hj : j ≤ 2) :
    (OAI.Erdos3.weylBudgetPolynomial j).natDegree < 256 := by
  have hne : OAI.Erdos3.weylBudgetPolynomial j ≠ 0 := by
    intro h
    have h1 := OAI.Erdos3.weylBudgetPolynomial_eval j 1
    rw [h, eval_zero] at h1
    exact (OAI.Erdos3.weylBudget_pos j (by decide : 0 < 1)).ne' h1.symm
  have hle := two_pow_natDegree_le_eval_two _ hne
  rw [OAI.Erdos3.weylBudgetPolynomial_eval] at hle
  have hlt := hle.trans_lt (weylBudget_two_lt j hj)
  by_contra hge
  push_neg at hge
  have h256 : (2 : Nat) ^ 128 * 2 ^ 128 ≤ 2 ^ (OAI.Erdos3.weylBudgetPolynomial j).natDegree := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) hge
  omega

end LeanProofs.GowersSzemeredi
