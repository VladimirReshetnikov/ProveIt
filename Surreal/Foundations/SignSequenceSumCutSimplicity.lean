import Surreal.Foundations.SignSequenceAddGroup

/-!
# Recognizing separators of the Conway sum cut

For arbitrary small presentations of two summands, a candidate separates
the sum cut exactly when subtracting each summand realizes the other cut.
The addition simplicity theorem then gives the sum as a sign prefix of
that candidate. This retains cut realization, rather than replacing it by
the weaker assertion that the summands are prefixes of the differences.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Translated cut realization characterizes realization of the sum cut. -/
theorem sumCut_realizes_iff_sub
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) (z : SignSequence.{u}) :
    (sumCut c d).IsRealizedBy z ↔
      c.IsRealizedBy (z - cut d) ∧ d.IsRealizedBy (z - cut c) := by
  rw [sumCut_realizes_iff]
  constructor
  · rintro ⟨⟨hcl, hdl⟩, ⟨hcr, hdr⟩⟩
    refine ⟨⟨fun i => lt_sub_iff_add_lt.mpr (hcl i),
      fun i => sub_lt_iff_lt_add.mpr (hcr i)⟩, ?_⟩
    constructor
    · intro i
      exact lt_sub_iff_add_lt.mpr (by simpa only [add_comm] using hdl i)
    · intro i
      exact sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using hdr i)
  · rintro ⟨hc, hd⟩
    refine ⟨⟨fun i => lt_sub_iff_add_lt.mp (hc.1 i), ?_⟩,
      ⟨fun i => sub_lt_iff_lt_add.mp (hc.2 i), ?_⟩⟩
    · intro i
      simpa only [add_comm] using lt_sub_iff_add_lt.mp (hd.1 i)
    · intro i
      simpa only [add_comm] using sub_lt_iff_lt_add.mp (hd.2 i)

/-- If each translated candidate realizes the other summand's cut, the
actual sum is a prefix of that candidate. -/
theorem sum_isPrefix_of_sub_realizes
    (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) (z : SignSequence.{u})
    (hc : c.IsRealizedBy (z - cut d)) (hd : d.IsRealizedBy (z - cut c)) :
    IsPrefix (cut c + cut d) z := by
  rw [← cut_sumCut]
  exact cut_isPrefix _ z ((sumCut_realizes_iff_sub c d z).mpr ⟨hc, hd⟩)

end

end Surreal.Foundations.SignSequence
