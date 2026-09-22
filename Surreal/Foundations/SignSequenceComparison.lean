import Surreal.Foundations.SignSequenceOptions

/-!
# Conway comparison on the sign carrier

The numerical order on sign sequences satisfies the recursive Conway
comparison rule with the canonical truncation options (`found:eq:comparison`).
The carrier is already extensional, so this result concerns equality and
order of numbers rather than a preorder or equivalence of raw games.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- Conway's comparison rule for the actual canonical sign options. -/
theorem le_iff_options_lt (x y : SignSequence.{u}) :
    x ≤ y ↔ (∀ i : LeftIndex x, leftOption x i < y) ∧
      (∀ i : RightIndex y, x < rightOption y i) := by
  constructor
  · intro h
    exact ⟨fun i => (leftOption_lt x i).trans_le h,
      fun i => h.trans_lt (lt_rightOption y i)⟩
  · rintro ⟨hl, hr⟩
    by_contra! hyx
    obtain ⟨b, hag, hsign⟩ := (lt_iff y x).mp hyx
    rcases SignType.trichotomy (x.signAt b) with hn | hz | hp
    · rw [hn] at hsign
      exact (not_lt_of_ge (SignType.neg_one_le _)) hsign
    · have hyn : y.signAt b = -1 := SignType.neg_iff.mp (by simpa [hz] using hsign)
      have hb : b < y.birthday := (y.signAt_ne_zero_iff b).mp (by simp [hyn])
      have heq : x = truncate y b hb.le :=
        eq_truncate_of_agree_of_zero y x b hb.le (fun j hj => (hag j hj).symm) hz
      have hc := hr ⟨⟨b, hb⟩, hyn⟩
      change x < truncate y b hb.le at hc
      exact (ne_of_lt hc) heq
    · have hb : b < x.birthday := (x.signAt_ne_zero_iff b).mp (by simp [hp])
      have hy0 : y.signAt b ≤ 0 := SignType.nonpos_iff_ne_one.mpr (by
        intro heq
        simp [hp, heq] at hsign)
      have hle : y ≤ truncate x b hb.le :=
        le_truncate_of_agree x y b hb.le hag hy0
      exact (not_le_of_gt (hl ⟨⟨b, hb⟩, hp⟩)) hle

/-- Strict comparison is witnessed by an option on one side. This is the
negation of the recursive non-strict comparison in the opposite direction. -/
theorem lt_iff_exists_option (x y : SignSequence.{u}) :
    x < y ↔ (∃ i : LeftIndex y, x ≤ leftOption y i) ∨
      (∃ i : RightIndex x, rightOption x i ≤ y) := by
  rw [← not_le, le_iff_options_lt]
  simp only [not_and_or, not_forall, not_lt]

/-- The recursive rule also holds for the lower-universe canonical cut
indices, so it can be used with the small-cut constructor. -/
theorem le_iff_canonicalCut (x y : SignSequence.{u}) :
    x ≤ y ↔ (∀ i, (canonicalCut x).left i < y) ∧
      (∀ i, x < (canonicalCut y).right i) := by
  rw [le_iff_options_lt]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨fun i => hl ((equivShrink (LeftIndex x)).symm i),
      fun i => hr ((equivShrink (RightIndex y)).symm i)⟩
  · rintro ⟨hl, hr⟩
    constructor
    · intro i
      simpa only [canonicalCut, Equiv.symm_apply_apply] using
        hl ((equivShrink (LeftIndex x)) i)
    · intro i
      simpa only [canonicalCut, Equiv.symm_apply_apply] using
        hr ((equivShrink (RightIndex y)) i)

end Surreal.Foundations.SignSequence
