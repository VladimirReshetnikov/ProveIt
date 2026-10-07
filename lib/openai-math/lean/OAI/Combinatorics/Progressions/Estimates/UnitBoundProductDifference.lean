/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Ring

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem norm_finset_prod_sub_prod_le_sum {ι A : Type*}
    [NormedCommRing A] [NormOneClass A]
    (s : Finset ι) (f g : ι → A)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod : ‖∏ i ∈ s, f i‖ ≤ 1 :=
      (s.norm_prod_le f).trans (Finset.prod_le_one₀ (fun i _ => norm_nonneg (f i)) hfs)
    have hga : ‖g a‖ ≤ 1 := hg a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      ‖f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i)‖ =
          ‖(f a - g a) * (∏ i ∈ s, f i) +
            g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := by congr 1; ring
      _ ≤ ‖(f a - g a) * (∏ i ∈ s, f i)‖ +
          ‖g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := norm_add_le _ _
      _ ≤ ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ +
          ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖f a - g a‖ * 1 + 1 * (∑ i ∈ s, ‖f i - g i‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
          (mul_le_mul hga (ih hfs hgs) (norm_nonneg _) (by norm_num))
      _ = ‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖ := by simp

theorem norm_prod_sub_prod_le_sum {ι A : Type*} [Fintype ι]
    [NormedCommRing A] [NormOneClass A]
    (f g : ι → A) (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) :
    ‖(∏ i, f i) - ∏ i, g i‖ ≤ ∑ i, ‖f i - g i‖ :=
  norm_finset_prod_sub_prod_le_sum Finset.univ f g (fun i _ => hf i) (fun i _ => hg i)

end Erdos3.VectorPolynomial

end

end OAI
