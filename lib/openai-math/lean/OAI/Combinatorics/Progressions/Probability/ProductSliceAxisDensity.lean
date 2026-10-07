/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.FiniteInnerProgressionFamily

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem piFinset_axis_subset {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    (A B : ∀ i, Finset (X i)) (hA : ∀ i, (A i).Nonempty)
    (hsub : Fintype.piFinset A ⊆ Fintype.piFinset B) (i : I) : A i ⊆ B i := by
  have hi := Finset.image_subset_image (f := fun x : ∀ i, X i => x i) hsub
  rw [Fintype.eval_image_piFinset A i (fun j _ => hA j)] at hi
  exact hi.trans (Fintype.eval_image_piFinset_subset B i)

theorem piFinset_card_ratio_le_axis {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    (A B : ∀ i, Finset (X i)) (hA : ∀ i, (A i).Nonempty) (hB : ∀ i, (B i).Nonempty)
    (hsub : Fintype.piFinset A ⊆ Fintype.piFinset B) (i : I) :
    ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card ≤
      ((A i).card : ℝ) / (B i).card := by
  let r : I → ℝ := fun j => ((A j).card : ℝ) / (B j).card
  have hr (j : I) : 0 ≤ r j ∧ r j ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    apply (div_le_one (by exact_mod_cast (hB j).card_pos : (0 : ℝ) < (B j).card)).mpr
    exact_mod_cast Finset.card_le_card (piFinset_axis_subset A B hA hsub j)
  have he : ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card = ∏ j, r j := by
    simp only [Fintype.card_piFinset, Nat.cast_prod, Finset.prod_div_distrib, r]
  rw [he, ← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i)]
  exact mul_le_of_le_one_right (hr i).1 (Finset.prod_le_one₀ (fun j _ => (hr j).1) (fun j _ => (hr j).2))

end Erdos3

end

end OAI
