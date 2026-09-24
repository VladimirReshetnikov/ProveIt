import Surreal.HahnSeries.PolynomialEvaluation
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Finite sumset bounds for polynomial evaluation

The finite-convolution support bounds used in `odg:def:prop:support`.
The natural scalar action on sets is repeated pointwise addition, so
`n • S` is the n-fold sumset and `0 • S = {0}`.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries
open scoped Pointwise

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- Each coefficient of a power arises from the corresponding finite sumset. -/
theorem support_pow_subset_sumset (a : K⟦Γ⟧) (S : Set Γ) (ha : a.support ⊆ S) (n : ℕ) :
    (a ^ n).support ⊆ n • S := by
  induction n with
  | zero => simp [Set.singleton_zero]
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact support_mul_subset.trans (Set.add_subset_add ih ha)

/-- A degree bound gives a finite union of sumsets for polynomial evaluation. -/
theorem support_polynomial_eval_subset (P : Polynomial K) (a : K⟦Γ⟧) (d : ℕ)
    (hd : P.natDegree ≤ d) (S : Set Γ) (ha : a.support ⊆ S) :
    (P.eval₂ _root_.HahnSeries.C a).support ⊆ ⋃ j ≤ d, j • S := by
  classical
  intro g hg
  change (P.eval₂ _root_.HahnSeries.C a).coeff g ≠ 0 at hg
  rw [Polynomial.eval₂_eq_sum_range, coeff_sum] at hg
  obtain ⟨j, hj, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
  have hm : g ∈ (_root_.HahnSeries.C (P.coeff j) * a ^ j).support := hterm
  rw [C_mul_eq_smul] at hm
  have hp := support_smul_subset (P.coeff j) (a ^ j) hm
  exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
    ⟨(Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hd,
      support_pow_subset_sumset a S ha j hp⟩⟩

/-- The support-ring evaluation inherits the same finite convolution bound. -/
theorem support_supportPolynomialEval_subset (P : Polynomial K)
    (a : nonpositiveSupportSubring Γ K) (d : ℕ) (hd : P.natDegree ≤ d) :
    (supportPolynomialEval a P).val.support ⊆ ⋃ j ≤ d, j • (a.val.support ∪ {0}) := by
  change (P.eval₂ nonpositiveConstants a).val.support ⊆ _
  rw [nonpositiveSupport_eval_val]
  exact support_polynomial_eval_subset P a.val d hd _ Set.subset_union_left

end
end Surreal.HahnSeries
