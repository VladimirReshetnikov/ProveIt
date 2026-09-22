import Surreal.Foundations.SmallNormalFormBirthday
import Surreal.Foundations.SmallNormalFormExtension

/-!
# Smallness of partial approximations to one actual surreal

Every partial approximation evaluates to a sign prefix of the same target.
Such prefixes are determined by their birthdays, and evaluation is injective.
Consequently all partial approximations, and in particular every chain of
them, form a small type in the universe of the target's birthday. No chosen
extraction process or surjectivity of evaluation is needed.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- The support length of a partial approximation is bounded by the target's birthday. -/
theorem Approximates.length_le_birthday {F : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (h : Approximates F x) : length F ≤ x.birthday :=
  length_le_birthday_of_cutEvaluation_isPrefix F x h.isPrefix

/-- Equal birthdays of two partial candidates force equal prefixes, hence equal forms. -/
theorem Approximates.eq_of_birthday_eq {F G : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (hF : Approximates F x) (hG : Approximates G x)
    (hb : (cutEvaluation F).birthday = (cutEvaluation G).birthday) : F = G := by
  apply cutEvaluation_injective
  apply IsPrefix.antisymm
  · refine ⟨hb.le, fun i hi => ?_⟩
    exact (hF.isPrefix.2 i hi).trans (hG.isPrefix.2 i (by simpa only [← hb] using hi)).symm
  · refine ⟨hb.ge, fun i hi => ?_⟩
    exact (hG.isPrefix.2 i hi).trans (hF.isPrefix.2 i (by simpa only [hb] using hi)).symm

/-- Candidate birthdays embed all partial approximations into a bounded ordinal interval. -/
def partialBirthdayEmbedding (x : SignSequence.{u}) :
    {F : SmallNormalForm.{u} // Approximates F x} ↪ Set.Iic x.birthday where
  toFun F := ⟨(cutEvaluation F.val).birthday, F.property.isPrefix.1⟩
  inj' := by
    intro F G h
    apply Subtype.ext
    exact F.property.eq_of_birthday_eq G.property (congrArg Subtype.val h)

/-- All partial approximations to one actual surreal form a small collection;
the statement is stronger than smallness of any one chain of partial forms. -/
instance small_partialApproximations (x : SignSequence.{u}) :
    Small.{u} {F : SmallNormalForm.{u} // Approximates F x} :=
  small_of_injective (partialBirthdayEmbedding x).injective

/-- Any set consisting of partial approximations is small, without a chain hypothesis. -/
theorem small_set_of_approximates (x : SignSequence.{u}) (s : Set SmallNormalForm.{u})
    (hs : ∀ F ∈ s, Approximates F x) : Small.{u} s := by
  apply small_of_injective
    (f := fun F : s => (⟨F.val, hs F.val F.property⟩ : {F // Approximates F x}))
  intro F G h
  exact Subtype.ext (congrArg (fun H : {F // Approximates F x} => H.val) h)

end

end Surreal.Foundations.SmallNormalForm
