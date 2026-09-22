import Surreal.Foundations.SignSequenceCutOperation
import Surreal.Foundations.SignSequenceComparison

/-!
# Comparison of arbitrary small cut values

The recursive comparison rule `found:eq:comparison` holds for any separated
small option presentations of the canonical simplest-number operation.
These theorems provide numerical comparisons for recursive arithmetic
without identifying a cut with a least upper bound.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- Conway comparison for arbitrary small separated option presentations. -/
theorem cut_le_cut_iff
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    cut c ≤ cut d ↔ (∀ i, c.left i < cut d) ∧ (∀ j, cut c < d.right j) := by
  constructor
  · intro h
    exact ⟨fun i => ((cut_realizes c).1 i).trans_le h,
      fun j => h.trans_lt ((cut_realizes d).2 j)⟩
  · rintro ⟨hl, hr⟩
    by_contra! hlt
    have hc : c.IsRealizedBy (cut d) :=
      ⟨hl, fun i => hlt.trans ((cut_realizes c).2 i)⟩
    have hd : d.IsRealizedBy (cut c) :=
      ⟨fun i => ((cut_realizes d).1 i).trans hlt, hr⟩
    have heq := IsPrefix.antisymm (cut_isPrefix c _ hc) (cut_isPrefix d _ hd)
    exact (ne_of_lt hlt) heq.symm

/-- Compare a small cut value to a number using the latter's canonical
right options. -/
theorem cut_le_iff (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (y : SignSequence.{u}) :
    cut c ≤ y ↔ (∀ i, c.left i < y) ∧ (∀ j : RightIndex y, cut c < rightOption y j) := by
  have h := cut_le_cut_iff c (canonicalCut y)
  simp only [cut_canonicalCut] at h
  rw [h]
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨hl, fun j => ?_⟩
    simpa only [canonicalCut, Equiv.symm_apply_apply] using
      hr ((equivShrink (RightIndex y)) j)
  · rintro ⟨hl, hr⟩
    exact ⟨hl, fun j => hr ((equivShrink (RightIndex y)).symm j)⟩

/-- Compare a number to a small cut value using the number's canonical
left options. -/
theorem le_cut_iff (x : SignSequence.{u})
    (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    x ≤ cut c ↔ (∀ i : LeftIndex x, leftOption x i < cut c) ∧ (∀ j, x < c.right j) := by
  have h := cut_le_cut_iff (canonicalCut x) c
  simp only [cut_canonicalCut] at h
  rw [h]
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨?_, hr⟩
    intro i
    simpa only [canonicalCut, Equiv.symm_apply_apply] using
      hl ((equivShrink (LeftIndex x)) i)
  · rintro ⟨hl, hr⟩
    exact ⟨fun i => hl ((equivShrink (LeftIndex x)).symm i), hr⟩

/-- Strict comparison of cut values has an option witness. -/
theorem cut_lt_cut_iff
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    cut c < cut d ↔ (∃ i, cut c ≤ d.left i) ∨ (∃ j, c.right j ≤ cut d) := by
  rw [← not_le, cut_le_cut_iff]
  simp only [not_and_or, not_forall, not_lt]

/-- Cofinal enlargement of left options and coinitial enlargement of right
bounds give the expected monotonicity between the corresponding cut values. -/
theorem cut_le_cut_of_options
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (hl : ∀ i, ∃ j, c.left i ≤ d.left j)
    (hr : ∀ j, ∃ i, c.right i ≤ d.right j) : cut c ≤ cut d := by
  apply (cut_le_cut_iff c d).mpr
  constructor
  · intro i
    obtain ⟨j, hij⟩ := hl i
    exact hij.trans_lt ((cut_realizes d).1 j)
  · intro j
    obtain ⟨i, hij⟩ := hr j
    exact ((cut_realizes c).2 i).trans_le hij

/-- Every canonical left option of a cut value is dominated by one of the
original left options. Otherwise that shorter sign would separate the cut. -/
theorem leftOption_cut_le (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (i : LeftIndex (cut c)) : ∃ j, leftOption (cut c) i ≤ c.left j := by
  by_contra! h
  have hx : c.IsRealizedBy (leftOption (cut c) i) :=
    ⟨h, fun j => (leftOption_lt (cut c) i).trans ((cut_realizes c).2 j)⟩
  exact (not_le_of_gt i.val.property) (cut_isPrefix c _ hx).1

/-- Every canonical right option is above one of the original right
options. This is the dual coinitiality statement. -/
theorem le_rightOption_cut (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (i : RightIndex (cut c)) : ∃ j, c.right j ≤ rightOption (cut c) i := by
  by_contra! h
  have hx : c.IsRealizedBy (rightOption (cut c) i) :=
    ⟨fun j => ((cut_realizes c).1 j).trans (lt_rightOption (cut c) i), h⟩
  exact (not_le_of_gt i.val.property) (cut_isPrefix c _ hx).1

end Surreal.Foundations.SignSequence
