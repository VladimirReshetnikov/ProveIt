/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def dilateMvPolynomial {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ m ∈ p.support, MvPolynomial.monomial m
    (p.coeff m * ∏ i ∈ m.support, R ^ m i)

theorem dilateMvPolynomial_coeff {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) (m : ι →₀ ℕ) :
    (dilateMvPolynomial R p).coeff m =
      p.coeff m * ∏ i ∈ m.support, R ^ m i := by
  classical
  rw [dilateMvPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [MvPolynomial.notMem_support_iff.mp h, zero_mul]

theorem dilateMvPolynomial_support_subset {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) :
    (dilateMvPolynomial R p).support ⊆ p.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, dilateMvPolynomial_coeff] at hm
  exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)

theorem dilateMvPolynomial_degree_le {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ)
    (i : ι) {d : ℕ} (hp : p.degreeOf i ≤ d) : (dilateMvPolynomial R p).degreeOf i ≤ d := by
  rw [MvPolynomial.degreeOf_le_iff] at hp ⊢
  exact fun m hm => hp m (dilateMvPolynomial_support_subset R p hm)

theorem dilateMvPolynomial_eval {ι : Type*} (R : ℝ) (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (dilateMvPolynomial R p) = MvPolynomial.eval (R • x) p := by
  classical
  rw [dilateMvPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval_monomial]
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem dilateMvPolynomial_coeff_abs_le {ι : Type*} {R : ℝ} (hR : 1 ≤ R)
    (p : MvPolynomial ι ℝ) (m : ι →₀ ℕ) :
    |p.coeff m| ≤ |(dilateMvPolynomial R p).coeff m| := by
  have hw : 1 ≤ ∏ i ∈ m.support, R ^ m i := by
    calc
      1 = ∏ _i ∈ m.support, (1 : ℝ) := by simp
      _ ≤ ∏ i ∈ m.support, R ^ m i := Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
        (fun index _ => one_le_pow₀ hR)
  rw [dilateMvPolynomial_coeff, abs_mul, abs_of_nonneg (zero_le_one.trans hw)]
  exact le_mul_of_one_le_right (abs_nonneg _) hw

end Erdos3

end

end OAI
