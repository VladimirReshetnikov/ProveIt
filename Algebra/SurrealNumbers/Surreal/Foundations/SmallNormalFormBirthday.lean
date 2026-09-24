import Surreal.Foundations.SmallNormalFormComparison

/-!
# Support length is bounded by the candidate's birthday

Every proper ordinal truncation has a distinct canonical value and is a
sign prefix of the full value. Its birthday is therefore strictly smaller.
Ordinal induction bounds the formal support length by the birthday of the
candidate, and hence by the birthday of any actual sign sequence extending
that candidate. This supplies a termination bound for later extraction
constructions; it does not construct an extraction process itself.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- Ordinal truncations, including indices past the support length, evaluate to prefixes. -/
theorem cutEvaluation_truncIdx_isPrefix (F : SmallNormalForm.{u}) (i : Ordinal.{u}) :
    IsPrefix (cutEvaluation (truncIdx F i)) (cutEvaluation F) := by
  by_cases hi : i < length F
  · rw [truncIdx_eq_trunc F ⟨i, hi⟩]
    exact cutEvaluation_trunc_isPrefix F _
  · rw [truncIdx_of_length_le F (le_of_not_gt hi)]
    exact IsPrefix.refl _

/-- A proper ordinal truncation has a proper-prefix candidate. -/
theorem cutEvaluation_truncIdx_simpler (F : SmallNormalForm.{u}) {i : Ordinal.{u}}
    (hi : i < length F) : Simpler (cutEvaluation (truncIdx F i)) (cutEvaluation F) := by
  have hp := cutEvaluation_truncIdx_isPrefix F i
  have hne : cutEvaluation (truncIdx F i) ≠ cutEvaluation F := by
    apply cutEvaluation_injective.ne
    intro h
    exact (length_truncIdx_lt F hi).ne (congrArg length h)
  refine ⟨hp, lt_of_le_of_ne hp.1 ?_⟩
  intro h
  apply hne
  apply hp.antisymm
  exact ⟨h.ge, fun j hj => (hp.2 j (by simpa only [h] using hj)).symm⟩

/-- The birthdays of proper ordinal truncations are strictly smaller. -/
theorem birthday_cutEvaluation_truncIdx_lt (F : SmallNormalForm.{u}) {i : Ordinal.{u}}
    (hi : i < length F) :
    (cutEvaluation (truncIdx F i)).birthday < (cutEvaluation F).birthday :=
  (cutEvaluation_truncIdx_simpler F hi).2

/-- The lower-universe ordinal support length never exceeds the actual candidate's birthday. -/
theorem length_le_birthday_cutEvaluation (F : SmallNormalForm.{u}) :
    length F ≤ (cutEvaluation F).birthday := by
  induction F using (InvImage.wf length Ordinal.lt_wf).induction with
  | h F ih =>
    apply le_of_forall_lt
    intro i hi
    have hb := ih (truncIdx F i) (length_truncIdx_lt F hi)
    rw [length_truncIdx, min_eq_left hi.le] at hb
    exact hb.trans_lt (birthday_cutEvaluation_truncIdx_lt F hi)

/-- A candidate prefix of a fixed actual surreal has support length bounded
by that surreal's birthday. -/
theorem length_le_birthday_of_cutEvaluation_isPrefix (F : SmallNormalForm.{u})
    (x : SignSequence.{u}) (h : IsPrefix (cutEvaluation F) x) : length F ≤ x.birthday :=
  (length_le_birthday_cutEvaluation F).trans h.1

end

end Surreal.Foundations.SmallNormalForm
