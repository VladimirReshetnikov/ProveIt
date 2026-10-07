import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem translation_difference_zero_off {G : Type*} [AddCommGroup G] [DecidableEq G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0) (v x : G)
    (hx : x ∉ S ∪ S.image (fun y => y + v)) : w (x - v) - w x = 0 := by
  have hxS : x ∉ S := fun h => hx (Finset.mem_union_left _ h)
  have hyS : x - v ∉ S := by
    intro h
    apply hx
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x - v, h, sub_add_cancel x v⟩)
  rw [hw _ hyS, hw _ hxS, sub_self]

theorem finiteSupport_translation_l1_bound {G : Type*} [AddCommGroup G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0) (v : G)
    {B : ℝ} (hB : 0 ≤ B) (hstep : ∀ x, |w (x - v) - w x| ≤ B) :
    (∑' x, |w (x - v) - w x|) ≤ 2 * (S.card : ℝ) * B := by
  classical
  let U := S ∪ S.image (fun y => y + v)
  have hz (x : G) (hx : x ∉ U) : |w (x - v) - w x| = 0 := by
    rw [translation_difference_zero_off w S hw v x hx, abs_zero]
  have hc : (U.card : ℝ) ≤ 2 * (S.card : ℝ) := by
    have hn : U.card ≤ S.card + S.card :=
      (Finset.card_union_le S (S.image (fun y => y + v))).trans
        (Nat.add_le_add_left Finset.card_image_le _)
    exact_mod_cast (show U.card ≤ 2 * S.card by omega)
  calc
    (∑' x, |w (x - v) - w x|) = ∑ x ∈ U, |w (x - v) - w x| :=
      (hasSum_sum_of_ne_finset_zero hz).tsum_eq
    _ ≤ ∑ _x ∈ U, B := Finset.sum_le_sum (fun x _ => hstep x)
    _ = (U.card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hB

end Erdos3

end

end OAI
