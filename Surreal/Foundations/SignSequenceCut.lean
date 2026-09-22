import Surreal.Foundations.SignSequenceOptions
import Mathlib.Order.CompleteLattice.PiLex
import Mathlib.Data.Fintype.Order

/-!
# Filling small separated cuts of sign sequences

This constructs the small-cut-filler property of `found:sub:cutdata` for the
canonical sign carrier of `found:sub:signs`. A common strict bound on option
birthdays reduces the construction to the complete lexicographic order on
Boolean words of that fixed ordinal length. No unrestricted cut-filling
operation or field structure is assumed.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

private abbrev FullWord (b : Ordinal.{u}) := Lex (Set.Iio b → Bool)

private theorem signAt_ofSigns_lt (b : Ordinal.{u}) (f : Set.Iio b → Bool)
    (i : Ordinal.{u}) (hi : i < b) :
    (ofSigns b f).signAt i = if f ⟨i, hi⟩ then 1 else -1 :=
  signAt_ofSigns b f ⟨i, hi⟩

private theorem ofSigns_strictMono (b : Ordinal.{u}) :
    StrictMono (fun f : FullWord b => ofSigns b (ofLex f)) := by
  rintro f g ⟨i, hag, hlt⟩
  apply (lt_iff _ _).mpr
  refine ⟨i.val, ?_, ?_⟩
  · intro j hj
    rw [signAt_ofSigns_lt b _ j (hj.trans i.property),
      signAt_ofSigns_lt b _ j (hj.trans i.property)]
    exact congrArg (fun s : Bool => if s then (1 : SignType) else -1)
      (hag ⟨j, hj.trans i.property⟩ hj)
  · rw [signAt_ofSigns b _ i, signAt_ofSigns b _ i]
    obtain ⟨hf, hg⟩ := Bool.lt_iff.mp hlt
    simp [hf, hg]

private def fullWordEmbedding (b : Ordinal.{u}) : FullWord b ↪o SignSequence.{u} :=
  OrderEmbedding.ofStrictMono _ (ofSigns_strictMono b)

private def aboveWord (x : SignSequence.{u}) (b : Ordinal.{u}) : FullWord b :=
  toLex (fun i => if i.val < x.birthday then decide (x.signAt i = 1)
    else decide (i.val = x.birthday))

private theorem signAt_aboveWord_before (x : SignSequence.{u}) (b i : Ordinal.{u})
    (hi : i < x.birthday) (hib : i < b) :
    (fullWordEmbedding b (aboveWord x b)).signAt i = x.signAt i := by
  change (ofSigns b _).signAt i = _
  rw [signAt_ofSigns_lt b _ i hib]
  simp only [aboveWord, ofLex_toLex, if_pos hi]
  rcases SignType.trichotomy (x.signAt i) with hn | hz | hp
  · simp [hn]
  · exact False.elim (((x.signAt_ne_zero_iff i).mpr hi) hz)
  · simp [hp]

private theorem signAt_aboveWord_end (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : x.birthday < b) :
    (fullWordEmbedding b (aboveWord x b)).signAt x.birthday = 1 := by
  change (ofSigns b _).signAt _ = _
  rw [signAt_ofSigns_lt b _ _ hb]
  simp [aboveWord]

private theorem signAt_aboveWord_after (x : SignSequence.{u}) (b i : Ordinal.{u})
    (hi : x.birthday < i) (hib : i < b) :
    (fullWordEmbedding b (aboveWord x b)).signAt i = -1 := by
  change (ofSigns b _).signAt _ = _
  rw [signAt_ofSigns_lt b _ _ hib]
  simp [aboveWord, hi.not_gt, hi.ne']

private theorem lt_aboveWord (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : x.birthday < b) : x < fullWordEmbedding b (aboveWord x b) := by
  apply (lt_iff _ _).mpr
  refine ⟨x.birthday, fun i hi => (signAt_aboveWord_before x b i hi (hi.trans hb)).symm, ?_⟩
  rw [(x.signAt_eq_zero_iff _).mpr le_rfl, signAt_aboveWord_end x b hb]
  decide

/-- The completion is the least full word above the shorter sequence. -/
private theorem aboveWord_le_of_lt (x y : SignSequence.{u}) (b : Ordinal.{u})
    (hx : x.birthday < b) (hy : y.birthday ≤ b) (hxy : x < y) :
    fullWordEmbedding b (aboveWord x b) ≤ y := by
  obtain ⟨i, hag, hi⟩ := (lt_iff x y).mp hxy
  by_cases hix : i < x.birthday
  · apply le_of_lt
    apply (lt_iff _ _).mpr
    refine ⟨i, ?_, ?_⟩
    · intro j hj
      exact (signAt_aboveWord_before x b j (hj.trans hix) (hj.trans (hix.trans hx))).trans
        (hag j hj)
    · simpa only [signAt_aboveWord_before x b i hix (hix.trans hx)] using hi
  · have hx0 : x.signAt i = 0 := (x.signAt_eq_zero_iff i).mpr (le_of_not_gt hix)
    have hyp : y.signAt i = 1 := SignType.pos_iff.mp (hx0 ▸ hi)
    have hiy : i < y.birthday := (y.signAt_ne_zero_iff i).mp (by simp [hyp])
    have hieq : i = x.birthday := by
      apply le_antisymm _ (le_of_not_gt hix)
      by_contra! hshort
      have hn := (y.signAt_ne_zero_iff x.birthday).mpr (hshort.trans hiy)
      rw [← hag _ hshort, (x.signAt_eq_zero_iff _).mpr le_rfl] at hn
      exact hn rfl
    subst i
    apply Pi.toLex_monotone
    intro j
    by_cases hj : j < b
    · rcases lt_trichotomy j x.birthday with hlt | rfl | hgt
      · rw [signAt_aboveWord_before x b j hlt hj, hag j hlt]
      · rw [signAt_aboveWord_end x b hx, hyp]
      · rw [signAt_aboveWord_after x b j hgt hj]
        exact SignType.neg_one_le _
    · have hbj := le_of_not_gt hj
      rw [((fullWordEmbedding b (aboveWord x b)).signAt_eq_zero_iff j).mpr hbj,
        (y.signAt_eq_zero_iff j).mpr (hy.trans hbj)]

private theorem aboveWord_lt_of_lt (x y : SignSequence.{u}) (b : Ordinal.{u})
    (hx : x.birthday < b) (hy : y.birthday < b) (hxy : x < y) :
    fullWordEmbedding b (aboveWord x b) < y := by
  apply lt_of_le_of_ne (aboveWord_le_of_lt x y b hx hy.le hxy)
  intro heq
  have h := congrArg birthday heq
  exact hy.ne' h

private def belowWord (x : SignSequence.{u}) (b : Ordinal.{u}) : FullWord b :=
  toLex (fun i => !(aboveWord (-x) b i))

private theorem belowWord_eq_neg (x : SignSequence.{u}) (b : Ordinal.{u}) :
    fullWordEmbedding b (belowWord x b) = -fullWordEmbedding b (aboveWord (-x) b) := by
  apply ext
  intro i
  by_cases hi : i < b
  · change (ofSigns b _).signAt i = -(ofSigns b _).signAt i
    rw [signAt_ofSigns_lt b _ i hi, signAt_ofSigns_lt b _ i hi]
    change (if !(aboveWord (-x) b ⟨i, hi⟩) then (1 : SignType) else -1) =
      -(if aboveWord (-x) b ⟨i, hi⟩ then 1 else -1)
    cases aboveWord (-x) b ⟨i, hi⟩ <;> decide
  · rw [((fullWordEmbedding b (belowWord x b)).signAt_eq_zero_iff i).mpr
        (le_of_not_gt hi), signAt_neg,
      ((fullWordEmbedding b (aboveWord (-x) b)).signAt_eq_zero_iff i).mpr
        (le_of_not_gt hi)]
    rfl

private theorem belowWord_lt (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : x.birthday < b) : fullWordEmbedding b (belowWord x b) < x := by
  rw [belowWord_eq_neg]
  simpa only [neg_neg] using (neg_lt_neg_iff _ _).mpr (lt_aboveWord (-x) b hb)

private theorem aboveWord_le_belowWord (x y : SignSequence.{u}) (b : Ordinal.{u})
    (hx : x.birthday < b) (hy : y.birthday < b) (hxy : x < y) :
    aboveWord x b ≤ belowWord y b := by
  apply (fullWordEmbedding b).le_iff_le.mp
  apply aboveWord_le_of_lt x _ b hx le_rfl
  rw [belowWord_eq_neg]
  have h := aboveWord_lt_of_lt (-y) (-x) b hy hx ((neg_lt_neg_iff _ _).mpr hxy)
  simpa only [neg_neg] using (neg_lt_neg_iff _ _).mpr h

/-- A separated cut whose options have birthdays strictly below `b` has a
separator of birthday exactly `b`. The bound need not be a successor. -/
theorem exists_cut_separator_of_birthday_lt
    (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) (b : Ordinal.{u})
    (hleft : ∀ i, (c.left i).birthday < b)
    (hright : ∀ i, (c.right i).birthday < b) :
    ∃ x : SignSequence.{u}, x.birthday = b ∧ c.IsRealizedBy x := by
  let w : FullWord b := ⨆ i, aboveWord (c.left i) b
  refine ⟨fullWordEmbedding b w, rfl, ?_, ?_⟩
  · intro i
    exact (lt_aboveWord (c.left i) b (hleft i)).trans_le
      ((fullWordEmbedding b).monotone (le_iSup (fun i => aboveWord (c.left i) b) i))
  · intro j
    apply lt_of_le_of_lt ((fullWordEmbedding b).monotone ?_) (belowWord_lt _ b (hright j))
    exact iSup_le (fun i => aboveWord_le_belowWord _ _ b (hleft i) (hright j) (c.separated i j))

/-- Every small separated cut is filled by the constructed sign carrier.
The indices remain in the lower universe throughout. -/
theorem small_cut_fillers :
    HasSmallCutFillers.{u, u + 1} SignSequence.{u} (· < ·) := by
  intro c
  obtain ⟨b, hb⟩ := birthdays_bounded (Sum.elim c.left c.right)
  obtain ⟨x, _, hx⟩ := exists_cut_separator_of_birthday_lt c b
    (fun i => hb (Sum.inl i)) (fun j => hb (Sum.inr j))
  exact ⟨x, hx⟩

end

end Surreal.Foundations.SignSequence
