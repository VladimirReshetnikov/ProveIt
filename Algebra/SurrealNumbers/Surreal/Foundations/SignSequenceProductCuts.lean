import Surreal.Foundations.SignSequenceMultiplication
import Mathlib.Tactic.Linarith

/-!
# Multiplication of arbitrary small cut presentations

Conway's four-family product equation `found:eq:mulcut` holds for any
small separated presentations of the factors. Canonical left options are
dominated by original left options, and canonical right options are above
original right options. The rectangle formula transfers these comparisons
to product options; mutual prefix simplicity then gives equality.

This presentation independence is also needed by genetic root constructions,
whose option families need not be canonical.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

theorem mulOption_mono_left {x y a a' b : SignSequence.{u}}
    (ha : a ≤ a') (hb : b ≤ y) : mulOption x y a b ≤ mulOption x y a' b := by
  have h := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  dsimp only [mulOption]
  nlinarith

theorem mulOption_anti_left {x y a a' b : SignSequence.{u}}
    (ha : a ≤ a') (hb : y ≤ b) : mulOption x y a' b ≤ mulOption x y a b := by
  have h := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  dsimp only [mulOption]
  nlinarith

theorem mulOption_mono_right {x y a b b' : SignSequence.{u}}
    (ha : a ≤ x) (hb : b ≤ b') : mulOption x y a b ≤ mulOption x y a b' := by
  have h := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  dsimp only [mulOption]
  nlinarith

theorem mulOption_anti_right {x y a b b' : SignSequence.{u}}
    (ha : x ≤ a) (hb : b ≤ b') : mulOption x y a b' ≤ mulOption x y a b := by
  have h := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  dsimp only [mulOption]
  nlinarith

/-- Conway's product cut formed from arbitrary small factor presentations. -/
def productCut (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) where
  Left := (c.Left × d.Left) ⊕ (c.Right × d.Right)
  Right := (c.Left × d.Right) ⊕ (c.Right × d.Left)
  left := Sum.elim
    (fun p => mulOption (cut c) (cut d) (c.left p.1) (d.left p.2))
    (fun p => mulOption (cut c) (cut d) (c.right p.1) (d.right p.2))
  right := Sum.elim
    (fun p => mulOption (cut c) (cut d) (c.left p.1) (d.right p.2))
    (fun p => mulOption (cut c) (cut d) (c.right p.1) (d.left p.2))
  separated i j := by
    have hl : Sum.elim
        (fun p : c.Left × d.Left => mulOption (cut c) (cut d) (c.left p.1) (d.left p.2))
        (fun p : c.Right × d.Right => mulOption (cut c) (cut d) (c.right p.1) (d.right p.2)) i <
          cut c * cut d := by
      rcases i with ⟨i, j⟩ | ⟨i, j⟩
      · exact mulOption_lt_mul_of_lt_of_lt ((cut_realizes c).1 i) ((cut_realizes d).1 j)
      · exact mulOption_lt_mul_of_gt_of_gt ((cut_realizes c).2 i) ((cut_realizes d).2 j)
    have hr : cut c * cut d < Sum.elim
        (fun p : c.Left × d.Right => mulOption (cut c) (cut d) (c.left p.1) (d.right p.2))
        (fun p : c.Right × d.Left => mulOption (cut c) (cut d) (c.right p.1) (d.left p.2)) j := by
      rcases j with ⟨i, j⟩ | ⟨i, j⟩
      · exact mul_lt_mulOption_of_lt_of_gt ((cut_realizes c).1 i) ((cut_realizes d).2 j)
      · exact mul_lt_mulOption_of_gt_of_lt ((cut_realizes c).2 i) ((cut_realizes d).1 j)
    exact hl.trans hr

/-- All four inequalities in the generalized product presentation. -/
theorem productCut_realizes_iff
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) (z : SignSequence.{u}) :
    (productCut c d).IsRealizedBy z ↔
      ((∀ i j, mulOption (cut c) (cut d) (c.left i) (d.left j) < z) ∧
       (∀ i j, mulOption (cut c) (cut d) (c.right i) (d.right j) < z)) ∧
      ((∀ i j, z < mulOption (cut c) (cut d) (c.left i) (d.right j)) ∧
       (∀ i j, z < mulOption (cut c) (cut d) (c.right i) (d.left j))) := by
  simp only [SmallCutData.IsRealizedBy, productCut, Sum.forall,
    Sum.elim_inl, Sum.elim_inr, Prod.forall]

/-- The actual product separates every option of the generalized cut. -/
theorem productCut_realized
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    (productCut c d).IsRealizedBy (cut c * cut d) :=
  (productCut_realizes_iff c d _).mpr
    ⟨⟨fun i j => mulOption_lt_mul_of_lt_of_lt ((cut_realizes c).1 i) ((cut_realizes d).1 j),
      fun i j => mulOption_lt_mul_of_gt_of_gt ((cut_realizes c).2 i) ((cut_realizes d).2 j)⟩,
      ⟨fun i j => mul_lt_mulOption_of_lt_of_gt ((cut_realizes c).1 i) ((cut_realizes d).2 j),
      fun i j => mul_lt_mulOption_of_gt_of_lt ((cut_realizes c).2 i) ((cut_realizes d).1 j)⟩⟩

/-- Any separator of the generalized options also separates the canonical
product options. Only the valid directions of option cofinality are used. -/
theorem productCut_realizes_mulCut
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (z : SignSequence.{u}) (hz : (productCut c d).IsRealizedBy z) :
    (mulCut (cut c) (cut d)).IsRealizedBy z := by
  obtain ⟨⟨hll, hrr⟩, ⟨hlr, hrl⟩⟩ := (productCut_realizes_iff c d z).mp hz
  constructor
  · intro k
    change mulLeft (cut c) (cut d) ((equivShrink _).symm k) < z
    rcases (equivShrink _).symm k with ⟨i, j⟩ | ⟨i, j⟩
    · obtain ⟨i', hi⟩ := leftOption_cut_le c i
      obtain ⟨j', hj⟩ := leftOption_cut_le d j
      exact ((mulOption_mono_left hi (leftOption_lt (cut d) j).le).trans
        (mulOption_mono_right ((cut_realizes c).1 i').le hj)).trans_lt (hll i' j')
    · obtain ⟨i', hi⟩ := le_rightOption_cut c i
      obtain ⟨j', hj⟩ := le_rightOption_cut d j
      exact ((mulOption_anti_left hi (lt_rightOption (cut d) j).le).trans
        (mulOption_anti_right ((cut_realizes c).2 i').le hj)).trans_lt (hrr i' j')
  · intro k
    change z < mulRight (cut c) (cut d) ((equivShrink _).symm k)
    rcases (equivShrink _).symm k with ⟨i, j⟩ | ⟨i, j⟩
    · obtain ⟨i', hi⟩ := leftOption_cut_le c i
      obtain ⟨j', hj⟩ := le_rightOption_cut d j
      exact (hlr i' j').trans_le
        ((mulOption_anti_left hi ((cut_realizes d).2 j').le).trans
          (mulOption_mono_right (leftOption_lt (cut c) i).le hj))
    · obtain ⟨i', hi⟩ := le_rightOption_cut c i
      obtain ⟨j', hj⟩ := leftOption_cut_le d j
      exact (hrl i' j').trans_le
        ((mulOption_mono_left hi ((cut_realizes d).1 j').le).trans
          (mulOption_anti_right (lt_rightOption (cut c) i).le hj))

/-- Conway's product equation holds for arbitrary small separated
presentations, including redundant options. -/
theorem cut_productCut
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    cut (productCut c d) = cut c * cut d := by
  apply IsPrefix.antisymm (cut_isPrefix _ _ (productCut_realized c d))
  rw [mul_eq_cut]
  exact cut_isPrefix _ _ (productCut_realizes_mulCut c d _ (cut_realizes _))

/-- A separator of a product presentation extends its actual field product
in the sign-prefix order. -/
theorem productCut_isPrefix_of_realizes
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) (z : SignSequence.{u})
    (hz : (productCut c d).IsRealizedBy z) : IsPrefix (cut c * cut d) z := by
  rw [← cut_productCut]
  exact cut_isPrefix _ _ hz

end

end Surreal.Foundations.SignSequence
