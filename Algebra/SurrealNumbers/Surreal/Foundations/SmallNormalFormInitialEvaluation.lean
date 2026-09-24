import Surreal.Foundations.SmallNormalFormInitialSegment
import Surreal.Foundations.SmallNormalFormExtension

/-!
# Evaluating formal initial segments

Initial segments evaluate to sign prefixes. Their recursive centers agree
at every retained exponent, so approximation of an actual target restricts
to each formal initial segment. No additive compatibility is assumed.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

noncomputable section

theorem IsInitialSegment.cutEvaluation_isPrefix {F G : SmallNormalForm.{u}}
    (h : IsInitialSegment F G) :
    SignSequence.IsPrefix (cutEvaluation F) (cutEvaluation G) := by
  rcases (isInitialSegment_iff_eq_or_trunc F G).mp h with rfl | ⟨a, _, rfl⟩
  · exact SignSequence.IsPrefix.refl _
  · exact cutEvaluation_trunc_isPrefix G a

theorem IsInitialSegment.cutEvaluationCenter_eq {F G : SmallNormalForm.{u}}
    (h : IsInitialSegment F G) {a : SignSequence.{u}} (ha : a ∈ support F) :
    cutEvaluationCenter F a = cutEvaluationCenter G a := by
  unfold cutEvaluationCenter
  rw [h.trunc_eq ha, h.coeff_eq ha]

/-- All center bounds for a larger formal form include those for each initial segment. -/
theorem Approximates.initialSegment {F G : SmallNormalForm.{u}} {x : SignSequence.{u}}
    (hG : Approximates G x) (hFG : IsInitialSegment F G) : Approximates F x := by
  intro a ha
  rw [hFG.cutEvaluationCenter_eq ha]
  exact hG a (hFG.support_subset ha)

end

end Surreal.Foundations.SmallNormalForm
