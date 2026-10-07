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

theorem mvPolynomial_eval_abs_le_sum_coeff {ι : Type*}
    (p : MvPolynomial ι ℝ) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |MvPolynomial.eval x p| ≤ ∑ m ∈ p.support, |p.coeff m| := by
  classical
  rw [MvPolynomial.eval_eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m _
  rw [abs_mul, Finset.abs_prod]
  have hprod : (∏ i ∈ m.support, |x i ^ m i|) ≤ 1 := by
    apply Finset.prod_le_one₀
    · exact fun _ _ => abs_nonneg _
    · intro i _
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hx i)
  exact mul_le_of_le_one_right (abs_nonneg _) hprod

theorem mvPolynomial_support_card_le {N d : ℕ}
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ i, p.degreeOf i ≤ d) :
    p.support.card ≤ (d + 1) ^ N := by
  classical
  let f : p.support → (Fin N → Fin (d + 1)) := fun m i =>
    ⟨m.val i, Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_iff.mp (hp i)) m.val m.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg Fin.val (congrFun hab i)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using h

theorem exists_coefficient_of_unit_box_value {N d : ℕ}
    (p : MvPolynomial (Fin N) ℝ) (hp : ∀ i, p.degreeOf i ≤ d)
    (x : Fin N → ℝ) (hx : ∀ i, |x i| ≤ 1) {v : ℝ} (hv : 0 < v)
    (hval : v ≤ |MvPolynomial.eval x p|) :
    ∃ m : Fin N →₀ ℕ, v / (d + 1 : ℝ) ^ N ≤ |p.coeff m| := by
  classical
  have hp0 : p ≠ 0 := by
    intro h
    simp only [h, map_zero, abs_zero] at hval
    linarith
  obtain ⟨m, _hm, hmax⟩ := p.support.exists_max_image
    (fun monomial => |p.coeff monomial|) (MvPolynomial.support_nonempty.mpr hp0)
  refine ⟨m, (div_le_iff₀ (by positivity : 0 < (d + 1 : ℝ) ^ N)).mpr ?_⟩
  have hcard : (p.support.card : ℝ) ≤ (d + 1 : ℝ) ^ N := by
    exact_mod_cast mvPolynomial_support_card_le p hp
  calc
    v ≤ |MvPolynomial.eval x p| := hval
    _ ≤ ∑ monomial ∈ p.support, |p.coeff monomial| := mvPolynomial_eval_abs_le_sum_coeff p x hx
    _ ≤ ∑ _monomial ∈ p.support, |p.coeff m| := Finset.sum_le_sum hmax
    _ = (p.support.card : ℝ) * |p.coeff m| := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d + 1 : ℝ) ^ N * |p.coeff m| :=
      mul_le_mul_of_nonneg_right hcard (abs_nonneg _)
    _ = _ := mul_comm _ _

end Erdos3

end

end OAI
