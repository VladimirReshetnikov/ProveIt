import Surreal.Foundations.SignSequenceAddition

/-!
# Arbitrary presentations and associativity of Conway addition

The addition equation `found:eq:addcut` holds for every small separated
presentation of each summand. Each canonical left option is dominated by an original left option, and
each canonical right option is above an original right option. Strict
translation transfers these comparisons to the sum cut. Mutual prefix simplicity identifies the
two resulting numbers.

Associativity then follows by birthday induction in the three arguments.
This uses only the recursively constructed addition and its strict order
preservation; no associative or group structure is assumed.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Addition of arbitrary small cut presentations. -/
def sumCut (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) where
  Left := c.Left ⊕ d.Left
  Right := c.Right ⊕ d.Right
  left := Sum.elim (fun i => c.left i + cut d) (fun i => cut c + d.left i)
  right := Sum.elim (fun i => c.right i + cut d) (fun i => cut c + d.right i)
  separated i j := by
    have hl : Sum.elim (fun i => c.left i + cut d) (fun i => cut c + d.left i) i <
        cut c + cut d := by
      cases i with
      | inl i => exact add_right_strictMono _ ((cut_realizes c).1 i)
      | inr i => exact add_left_strictMono _ ((cut_realizes d).1 i)
    have hr : cut c + cut d <
        Sum.elim (fun i => c.right i + cut d) (fun i => cut c + d.right i) j := by
      cases j with
      | inl j => exact add_right_strictMono _ ((cut_realizes c).2 j)
      | inr j => exact add_left_strictMono _ ((cut_realizes d).2 j)
    exact hl.trans hr

/-- The generalized addition cut exposes both option families. -/
theorem sumCut_realizes_iff
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) (z : SignSequence.{u}) :
    (sumCut c d).IsRealizedBy z ↔
      ((∀ i, c.left i + cut d < z) ∧ (∀ i, cut c + d.left i < z)) ∧
      ((∀ i, z < c.right i + cut d) ∧ (∀ i, z < cut c + d.right i)) := by
  simp only [SmallCutData.IsRealizedBy, sumCut, Sum.forall, Sum.elim_inl, Sum.elim_inr]

/-- Strict translation shows that the actual sum separates all generalized
addition options, including redundant presentation options. -/
theorem sumCut_realized
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    (sumCut c d).IsRealizedBy (cut c + cut d) :=
  (sumCut_realizes_iff c d _).mpr
    ⟨⟨fun i => add_right_strictMono _ ((cut_realizes c).1 i),
      fun i => add_left_strictMono _ ((cut_realizes d).1 i)⟩,
      ⟨fun i => add_right_strictMono _ ((cut_realizes c).2 i),
      fun i => add_left_strictMono _ ((cut_realizes d).2 i)⟩⟩

/-- Any separator of generalized addition options also separates the
canonical addition options. Only the valid direction of option cofinality
is required. -/
theorem sumCut_realizes_addCut
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (z : SignSequence.{u}) (hz : (sumCut c d).IsRealizedBy z) :
    (addCut (cut c) (cut d)).IsRealizedBy z := by
  obtain ⟨⟨hlc, hld⟩, ⟨hrc, hrd⟩⟩ := (sumCut_realizes_iff c d z).mp hz
  apply (addCut_realizes_iff _ _ _).mpr
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i
    obtain ⟨j, hij⟩ := leftOption_cut_le c i
    exact ((add_right_strictMono _).monotone hij).trans_lt (hlc j)
  · intro i
    obtain ⟨j, hij⟩ := leftOption_cut_le d i
    exact ((add_left_strictMono _).monotone hij).trans_lt (hld j)
  · intro i
    obtain ⟨j, hij⟩ := le_rightOption_cut c i
    exact (hrc j).trans_le ((add_right_strictMono _).monotone hij)
  · intro i
    obtain ⟨j, hij⟩ := le_rightOption_cut d i
    exact (hrd j).trans_le ((add_left_strictMono _).monotone hij)

/-- Conway's addition equation holds for arbitrary small separated
presentations of both summands. -/
theorem cut_sumCut
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    cut (sumCut c d) = cut c + cut d := by
  apply IsPrefix.antisymm (cut_isPrefix _ _ (sumCut_realized c d))
  rw [add_eq_cut]
  exact cut_isPrefix _ _ (sumCut_realizes_addCut c d _ (cut_realizes _))

private theorem forall_left_addCut (x y : SignSequence.{u}) (p : SignSequence.{u} → Prop) :
    (∀ i, p ((addCut x y).left i)) ↔
      (∀ i : LeftIndex x, p (leftOption x i + y)) ∧
      (∀ i : LeftIndex y, p (x + leftOption y i)) := by
  change (∀ i, p (addLeft x y ((equivShrink _).symm i))) ↔ _
  exact ((equivShrink (LeftIndex x ⊕ LeftIndex y)).symm.forall_congr_right
    (q := fun i => p (addLeft x y i))).trans (by
      simp only [addLeft, Sum.forall, Sum.elim_inl, Sum.elim_inr])

private theorem forall_right_addCut (x y : SignSequence.{u}) (p : SignSequence.{u} → Prop) :
    (∀ i, p ((addCut x y).right i)) ↔
      (∀ i : RightIndex x, p (rightOption x i + y)) ∧
      (∀ i : RightIndex y, p (x + rightOption y i)) := by
  change (∀ i, p (addRight x y ((equivShrink _).symm i))) ↔ _
  exact ((equivShrink (RightIndex x ⊕ RightIndex y)).symm.forall_congr_right
    (q := fun i => p (addRight x y i))).trans (by
      simp only [addRight, Sum.forall, Sum.elim_inl, Sum.elim_inr])

private theorem forall_left_canonicalCut (x : SignSequence.{u}) (p : SignSequence.{u} → Prop) :
    (∀ i, p ((canonicalCut x).left i)) ↔ ∀ i : LeftIndex x, p (leftOption x i) := by
  exact (equivShrink (LeftIndex x)).symm.forall_congr_right (q := fun i => p (leftOption x i))

private theorem forall_right_canonicalCut (x : SignSequence.{u}) (p : SignSequence.{u} → Prop) :
    (∀ i, p ((canonicalCut x).right i)) ↔ ∀ i : RightIndex x, p (rightOption x i) := by
  exact (equivShrink (RightIndex x)).symm.forall_congr_right (q := fun i => p (rightOption x i))

/-- Associativity of the recursively constructed Conway addition, proved
by well-founded induction on the birthdays of its three inputs. -/
theorem add_assoc (x y z : SignSequence.{u}) : (x + y) + z = x + (y + z) := by
  induction x using (InvImage.wf birthday Ordinal.lt_wf).induction generalizing y z with
  | h x ihx =>
    induction y using (InvImage.wf birthday Ordinal.lt_wf).induction generalizing z with
    | h y ihy =>
      induction z using (InvImage.wf birthday Ordinal.lt_wf).induction with
      | h z ihz =>
        have hl : (x + y) + z = cut (sumCut (addCut x y) (canonicalCut z)) := by
          simpa only [← add_eq_cut, cut_canonicalCut] using
            (cut_sumCut (addCut x y) (canonicalCut z)).symm
        have hr : x + (y + z) = cut (sumCut (canonicalCut x) (addCut y z)) := by
          simpa only [← add_eq_cut, cut_canonicalCut] using
            (cut_sumCut (canonicalCut x) (addCut y z)).symm
        rw [hl, hr]
        apply cut_congr
        intro w
        simp only [sumCut_realizes_iff, cut_canonicalCut, ← add_eq_cut]
        rw [forall_left_addCut x y (fun a => a + z < w),
          forall_right_addCut x y (fun a => w < a + z),
          forall_left_canonicalCut z (fun a => (x + y) + a < w),
          forall_right_canonicalCut z (fun a => w < (x + y) + a),
          forall_left_canonicalCut x (fun a => a + (y + z) < w),
          forall_right_canonicalCut x (fun a => w < a + (y + z)),
          forall_left_addCut y z (fun a => x + a < w),
          forall_right_addCut y z (fun a => w < x + a)]
        have hlx (i : LeftIndex x) := ihx (leftOption x i) i.val.property y z
        have hrx (i : RightIndex x) := ihx (rightOption x i) i.val.property y z
        have hly (i : LeftIndex y) := ihy (leftOption y i) i.val.property z
        have hry (i : RightIndex y) := ihy (rightOption y i) i.val.property z
        have hlz (i : LeftIndex z) := ihz (leftOption z i) i.val.property
        have hrz (i : RightIndex z) := ihz (rightOption z i) i.val.property
        simp only [hlx, hrx, hly, hry, hlz, hrz, and_assoc]

end

end Surreal.Foundations.SignSequence
