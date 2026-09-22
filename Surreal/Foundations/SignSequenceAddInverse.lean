import Surreal.Foundations.SignSequenceAddition
import Surreal.Foundations.SignSequenceRecursion

/-!
# Additive inverses on the sign carrier

The independently constructed sign reversal is the additive inverse for
Conway addition. This is proved by simplicity induction and the certified
addition option bounds, without assuming an additive group structure.
-/

universe u

namespace Surreal.Foundations.SignSequence

@[simp] theorem truncate_neg (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) : truncate (-x) b hb = -truncate x b hb := by
  apply ext
  intro i
  by_cases hi : i < b <;> simp [signAt_truncate, signAt_neg, hi]

/-- A left option of the sign reversal is the reversal of a right option. -/
theorem leftOption_neg (x : SignSequence.{u}) (i : LeftIndex (-x)) :
    ∃ j : RightIndex x, leftOption (-x) i = -rightOption x j := by
  have hs : x.signAt i.val.val = -1 := by
    have h := congrArg Neg.neg i.property
    simpa only [signAt_neg, _root_.neg_neg] using h
  refine ⟨⟨⟨i.val.val, i.val.property⟩, hs⟩, ?_⟩
  exact truncate_neg x _ i.val.property.le

/-- A right option of the sign reversal is the reversal of a left option. -/
theorem rightOption_neg (x : SignSequence.{u}) (i : RightIndex (-x)) :
    ∃ j : LeftIndex x, rightOption (-x) i = -leftOption x j := by
  have hs : x.signAt i.val.val = 1 := by
    have h := congrArg Neg.neg i.property
    simpa only [signAt_neg, _root_.neg_neg] using h
  refine ⟨⟨⟨i.val.val, i.val.property⟩, hs⟩, ?_⟩
  exact truncate_neg x _ i.val.property.le

/-- Conway addition cancels against sign reversal. The empty sequence
separates the addition cut, hence is its simplest separator. -/
@[simp] theorem add_neg_cancel (x : SignSequence.{u}) : x + -x = 0 := by
  induction x using simpler_wellFounded.induction with
  | h x ih =>
    rw [add_eq_cut]
    apply (cut_eq_iff _ 0).mpr
    refine ⟨?_, fun _ _ => bot_le⟩
    rw [addCut_realizes_iff]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro i
      have h := add_left_strictMono (leftOption x i)
        ((neg_lt_neg_iff _ _).mpr (leftOption_lt x i))
      dsimp only at h
      rw [ih _ (leftOption_simpler x i)] at h
      exact h
    · intro i
      obtain ⟨j, hj⟩ := leftOption_neg x i
      rw [hj]
      have h := add_right_strictMono (-rightOption x j) (lt_rightOption x j)
      dsimp only at h
      rw [ih _ (rightOption_simpler x j)] at h
      exact h
    · intro i
      have h := add_left_strictMono (rightOption x i)
        ((neg_lt_neg_iff _ _).mpr (lt_rightOption x i))
      dsimp only at h
      rw [ih _ (rightOption_simpler x i)] at h
      exact h
    · intro i
      obtain ⟨j, hj⟩ := rightOption_neg x i
      rw [hj]
      have h := add_right_strictMono (-leftOption x j) (leftOption_lt x j)
      dsimp only at h
      rw [ih _ (leftOption_simpler x j)] at h
      exact h

/-- Cancellation with the sign reversal on the left. -/
@[simp] theorem neg_add_cancel (x : SignSequence.{u}) : -x + x = 0 := by
  rw [add_comm, add_neg_cancel]

end Surreal.Foundations.SignSequence
