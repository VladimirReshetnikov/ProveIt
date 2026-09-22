import Surreal.Foundations.SignSequenceOptions

/-!
# Nested canonical options

Canonical sign options are truncations, so options from opposite sides
are nested: one is an option of the other. This supplies the separation
step in binary recursive arithmetic on the canonical sign carrier.
-/

universe u

namespace Surreal.Foundations.SignSequence

@[simp] theorem truncate_truncate (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) (c : Ordinal.{u}) (hc : c ≤ b) :
    truncate (truncate x b hb) c hc = truncate x c (hc.trans hb) := by
  apply ext
  intro i
  by_cases hi : i < c
  · simp only [signAt_truncate, if_pos hi, if_pos (hi.trans_le hc)]
  · simp only [signAt_truncate, if_neg hi]

@[simp] theorem truncate_birthday (x : SignSequence.{u}) :
    truncate x x.birthday le_rfl = x := by
  apply ext
  intro i
  by_cases hi : i < x.birthday
  · simp only [signAt_truncate, if_pos hi]
  · simp only [signAt_truncate, if_neg hi, (x.signAt_eq_zero_iff i).mpr (le_of_not_gt hi)]

/-- Prefixes are exactly the corresponding birthday truncations. -/
theorem IsPrefix.truncate_eq {x y : SignSequence.{u}} (h : IsPrefix x y) :
    truncate y x.birthday h.1 = x := by
  apply ext
  intro i
  by_cases hi : i < x.birthday
  · simp only [signAt_truncate, if_pos hi, h.2 i hi]
  · simp only [signAt_truncate, if_neg hi, (x.signAt_eq_zero_iff i).mpr (le_of_not_gt hi)]

/-- An earlier plus truncation is a left option of a later truncation. -/
theorem leftOption_of_truncate (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) (i : LeftIndex x) (hi : i.val.val < b) :
    ∃ k : LeftIndex (truncate x b hb), leftOption (truncate x b hb) k = leftOption x i := by
  let k : LeftIndex (truncate x b hb) :=
    ⟨⟨i.val.val, hi⟩, by simpa only [signAt_truncate, if_pos hi] using i.property⟩
  refine ⟨k, ?_⟩
  exact truncate_truncate x b hb i.val.val hi.le

/-- An earlier minus truncation is a right option of a later truncation. -/
theorem rightOption_of_truncate (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) (i : RightIndex x) (hi : i.val.val < b) :
    ∃ k : RightIndex (truncate x b hb), rightOption (truncate x b hb) k = rightOption x i := by
  let k : RightIndex (truncate x b hb) :=
    ⟨⟨i.val.val, hi⟩, by simpa only [signAt_truncate, if_pos hi] using i.property⟩
  refine ⟨k, ?_⟩
  exact truncate_truncate x b hb i.val.val hi.le

/-- Opposite canonical options are nested. One is a left option of the
other, or the other is its right option. Their truncation positions cannot
coincide, since a sign cannot be both plus and minus. -/
theorem left_right_option_nested (x : SignSequence.{u}) (i : LeftIndex x)
    (j : RightIndex x) :
    (∃ k : LeftIndex (rightOption x j), leftOption (rightOption x j) k = leftOption x i) ∨
      (∃ k : RightIndex (leftOption x i), rightOption (leftOption x i) k = rightOption x j) := by
  rcases lt_trichotomy i.val.val j.val.val with h | h | h
  · exact Or.inl (leftOption_of_truncate x _ j.val.property.le i h)
  · have hi := i.property
    rw [h, j.property] at hi
    cases hi
  · exact Or.inr (rightOption_of_truncate x _ i.val.property.le j h)

end Surreal.Foundations.SignSequence
