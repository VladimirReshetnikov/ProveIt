import Surreal.Foundations.SignSequence

/-!
# Canonical sign options and simplest separation

The canonical truncation options in `found:sub:signs` reconstruct the
sequence as their simplest separator: every other separator extends its
sign sequence, and hence cannot have a smaller birthday. This is a theorem
about the constructed carrier and its numerical order. It does not assume
or provide cut filling for arbitrary small option families.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- If the signs agree before a position where the second sequence ends,
the second sequence is that truncation. -/
theorem eq_truncate_of_agree_of_zero (x y : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) (hag : ∀ j < b, y.signAt j = x.signAt j)
    (hz : y.signAt b = 0) : y = truncate x b hb := by
  apply ext
  intro j
  by_cases hj : j < b
  · simpa only [signAt_truncate, if_pos hj] using hag j hj
  · rw [signAt_truncate, if_neg hj]
    exact (y.signAt_eq_zero_iff j).mpr
      (((y.signAt_eq_zero_iff b).mp hz).trans (le_of_not_gt hj))

/-- A nonpositive next symbol places an agreeing sequence below the truncation. -/
theorem le_truncate_of_agree (x y : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) (hag : ∀ j < b, y.signAt j = x.signAt j)
    (hs : y.signAt b ≤ 0) : y ≤ truncate x b hb := by
  rcases lt_or_eq_of_le hs with hn | hz
  · apply le_of_lt
    apply (lt_iff _ _).mpr
    refine ⟨b, ?_, ?_⟩
    · intro j hj
      simpa only [signAt_truncate, if_pos hj] using hag j hj
    · simpa only [signAt_truncate, lt_self_iff_false, if_false] using hn
  · exact (eq_truncate_of_agree_of_zero x y b hb hag hz).le

/-- A nonnegative next symbol places an agreeing sequence above the truncation. -/
theorem truncate_le_of_agree (x y : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) (hag : ∀ j < b, y.signAt j = x.signAt j)
    (hs : 0 ≤ y.signAt b) : truncate x b hb ≤ y := by
  rcases lt_or_eq_of_le hs with hp | hz
  · apply le_of_lt
    apply (lt_iff _ _).mpr
    refine ⟨b, ?_, ?_⟩
    · intro j hj
      simpa only [signAt_truncate, if_pos hj] using (hag j hj).symm
    · simpa only [signAt_truncate, lt_self_iff_false, if_false] using hp
  · exact (eq_truncate_of_agree_of_zero x y b hb hag hz.symm).ge

/-- Every separator of the canonical options extends the original sign
sequence. This is the simplicity conclusion in `found:sub:signs`. -/
theorem isPrefix_of_separates_options (x y : SignSequence.{u})
    (hleft : ∀ i : LeftIndex x, leftOption x i < y)
    (hright : ∀ i : RightIndex x, y < rightOption x i) : IsPrefix x y := by
  have heq : ∀ i, i < x.birthday → x.signAt i = y.signAt i := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro hi
      have hag : ∀ j < i, y.signAt j = x.signAt j :=
        fun j hj => (ih j hj (hj.trans hi)).symm
      rcases SignType.trichotomy (x.signAt i) with hn | hz | hp
      · have hyr : y < truncate x i hi.le := hright ⟨⟨i, hi⟩, hn⟩
        have hneg : y.signAt i < 0 := by
          by_contra! hnonneg
          exact (not_le_of_gt hyr) (truncate_le_of_agree x y i hi.le hag hnonneg)
        exact hn.trans (SignType.neg_iff.mp hneg).symm
      · exact False.elim (((x.signAt_ne_zero_iff i).mpr hi) hz)
      · have hyl : truncate x i hi.le < y := hleft ⟨⟨i, hi⟩, hp⟩
        have hpos : 0 < y.signAt i := by
          by_contra! hnonpos
          exact (not_le_of_gt hyl) (le_truncate_of_agree x y i hi.le hag hnonpos)
        exact hp.trans (SignType.pos_iff.mp hpos).symm
  refine ⟨?_, heq⟩
  by_contra! hshort
  have hn := (x.signAt_ne_zero_iff y.birthday).mpr hshort
  rw [heq _ hshort] at hn
  exact hn ((y.signAt_eq_zero_iff _).mpr le_rfl)

/-- The version using the actual lower-universe canonical cut data. -/
theorem canonicalCut_isPrefix (x y : SignSequence.{u})
    (hy : (canonicalCut x).IsRealizedBy y) : IsPrefix x y := by
  apply isPrefix_of_separates_options x y
  · intro i
    simpa only [canonicalCut, Equiv.symm_apply_apply] using
      hy.1 ((equivShrink (LeftIndex x)) i)
  · intro i
    simpa only [canonicalCut, Equiv.symm_apply_apply] using
      hy.2 ((equivShrink (RightIndex x)) i)

/-- The given sequence is the unique canonical-cut separator of minimum
birthday. Other separators, if any, have it as a proper sign prefix. -/
theorem canonicalCut_simplest (x : SignSequence.{u}) :
    (canonicalCut x).IsRealizedBy x ∧
      ∀ y, (canonicalCut x).IsRealizedBy y →
        x.birthday ≤ y.birthday ∧ (y.birthday ≤ x.birthday → y = x) := by
  refine ⟨canonicalCut_realized x, ?_⟩
  intro y hy
  have hxy := canonicalCut_isPrefix x y hy
  refine ⟨hxy.1, fun hlen => ?_⟩
  apply IsPrefix.antisymm ?_ hxy
  exact ⟨hlen, fun i hi => (hxy.2 i (hi.trans_le hlen)).symm⟩

end

end Surreal.Foundations.SignSequence
