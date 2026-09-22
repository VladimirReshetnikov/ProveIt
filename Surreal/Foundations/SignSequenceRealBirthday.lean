import Surreal.Foundations.SignSequenceReal
import Surreal.Foundations.SignSequenceGameBirthday
import Surreal.Foundations.SignSequenceDyadics

/-!
# Real numbers have birthday at most omega

Every ordinary real is represented by its cut of dyadic rationals. Those
options are short games, so the raw cut has birthday at most `ω`; the
canonical sign representative has no larger birthday.
The finite-birthday classification then shows that a non-dyadic ordinary
real has birthday exactly `ω`.

This is the real-coefficient bound used in the proof of `lem:realproduct`
in `docs/surreal/gonshor-laurent-birthdays/article.tex`. It does not assert
the exact finite dyadic formula `eq:realbirth`.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The raw dyadic Dedekind cut representing any ordinary real has birthday
at most `ω`. This proves the bound directly from its short dyadic options. -/
theorem real_toIGame_birthday_le_omega0 (r : ℝ) :
    (_root_.Real.toIGame.{u} r).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
  apply IGame.birthday_le_iff.mpr
  intro p a ha
  cases p with
  | left =>
    rw [_root_.Real.leftMoves_toIGame] at ha
    obtain ⟨q, _, rfl⟩ := ha
    exact IGame.Short.birthday_lt_omega0 _
  | right =>
    rw [_root_.Real.rightMoves_toIGame] at ha
    obtain ⟨q, _, rfl⟩ := ha
    exact IGame.Short.birthday_lt_omega0 _

/-- The actual sign birthday of every embedded ordinary real is at most
`ω`, as used in `lem:realproduct`. The comparison with the raw cut uses
proved minimality of the canonical sign representative. -/
theorem birthday_ofReal_le_omega0 (r : ℝ) :
    (ofReal r : SignSequence.{u}).birthday ≤ Ordinal.omega0 := by
  have h := birthday_le_of_toSurreal_eq_mk (ofReal r : SignSequence.{u})
    (_root_.Real.toIGame r) (toSurreal_ofReal r)
  exact h.trans (NatOrdinal.val.monotone (real_toIGame_birthday_le_omega0 r))

/-- An embedded ordinary real has finite birthday exactly when it is
dyadic, as stated in the real-coefficient subsection preceding
`eq:realbirth` of the Laurent-birthday document. -/
theorem birthday_ofReal_lt_omega0_iff (r : ℝ) :
    (ofReal r : SignSequence.{u}).birthday < Ordinal.omega0 ↔
      ∃ q : Dyadic, (q.toRat : ℝ) = r := by
  rw [birthday_lt_omega0_iff_dyadic]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, (ofReal_inj _ _).mp ?_⟩
    simpa only [ofReal_ratCast] using hq
  · rintro ⟨q, rfl⟩
    exact ⟨q, (ofReal_ratCast q.toRat).symm⟩

/-- Every non-dyadic ordinary real has birthday exactly `ω`, the assertion
preceding `eq:realbirth` and `eq:dyadic-birthday` in the two product-birthday
documents. No explicit finite dyadic birthday formula is used. -/
theorem birthday_ofReal_eq_omega0_of_not_dyadic (r : ℝ)
    (hr : ¬ ∃ q : Dyadic, (q.toRat : ℝ) = r) :
    (ofReal r : SignSequence.{u}).birthday = Ordinal.omega0 := by
  apply le_antisymm (birthday_ofReal_le_omega0 r)
  exact le_of_not_gt (fun h => hr ((birthday_ofReal_lt_omega0_iff r).mp h))

/-- Exact birthday `ω` characterizes the non-dyadic ordinary reals. -/
theorem birthday_ofReal_eq_omega0_iff (r : ℝ) :
    (ofReal r : SignSequence.{u}).birthday = Ordinal.omega0 ↔
      ¬ ∃ q : Dyadic, (q.toRat : ℝ) = r := by
  constructor
  · intro h hr
    have hlt := (birthday_ofReal_lt_omega0_iff.{u} r).mpr hr
    rw [h] at hlt
    exact (lt_irrefl _) hlt
  · exact birthday_ofReal_eq_omega0_of_not_dyadic r

/-- The ordinary real `1/3` has birthday exactly `ω`, as in the
non-dyadic examples following `eq:realbirth`. In particular, inversion
already leaves the finite-birthday fragment at the element `3`. -/
theorem birthday_one_third_eq_omega0 :
    (1 / 3 : SignSequence.{u}).birthday = Ordinal.omega0 := by
  apply le_antisymm
  · simpa only [ofReal_div, ofReal_one, map_ofNat] using
      birthday_ofReal_le_omega0.{u} (1 / 3 : ℝ)
  · exact le_of_not_gt not_birthday_one_third_lt_omega0

end

end Surreal.Foundations.SignSequence
