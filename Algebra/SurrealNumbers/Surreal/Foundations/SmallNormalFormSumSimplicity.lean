import Surreal.Foundations.SmallNormalFormExtension
import Surreal.Foundations.SignSequenceSumCutSimplicity

/-!
# Simplicity of sums of canonical normal-form candidates

The canonical valuation-ball presentation makes the full approximation
invariant equivalent to realizing the cut. Conway sum-cut simplicity then
supplies a prefix criterion needed to prove arithmetic compatibility.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- The small valuation-ball presentation of a canonical formal-form value. -/
def cutEvaluationCut (F : SmallNormalForm.{u}) :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) :=
  valuationBallCut (fun a : support F => cutEvaluationCenter F a.val)
    (fun a : support F => -a.val) (cutEvaluation_centers_compatible F)

@[simp] theorem cut_cutEvaluationCut (F : SmallNormalForm.{u}) :
    cut (cutEvaluationCut F) = cutEvaluation F := (cutEvaluation_eq_simplest F).symm

/-- The approximation invariant is the exact separator predicate of the cut. -/
theorem cutEvaluationCut_realizes_iff (F : SmallNormalForm.{u}) (x : SignSequence.{u}) :
    (cutEvaluationCut F).IsRealizedBy x ↔ Approximates F x := by
  rw [cutEvaluationCut, valuationBallCut_realizes_iff]
  constructor
  · intro h a ha
    exact h ⟨a, ha⟩
  · intro h a
    exact h a.val a.property

/-- Two translated approximation invariants force the sum to be a prefix.
This uses the full cut bounds; prefix relations alone would not suffice. -/
theorem cutEvaluation_add_isPrefix_of_approximates (F G : SmallNormalForm.{u})
    (z : SignSequence.{u}) (hF : Approximates F (z - cutEvaluation G))
    (hG : Approximates G (z - cutEvaluation F)) :
    IsPrefix (cutEvaluation F + cutEvaluation G) z := by
  have hc : (cutEvaluationCut F).IsRealizedBy (z - cut (cutEvaluationCut G)) := by
    rw [cut_cutEvaluationCut, cutEvaluationCut_realizes_iff]
    exact hF
  have hd : (cutEvaluationCut G).IsRealizedBy (z - cut (cutEvaluationCut F)) := by
    rw [cut_cutEvaluationCut, cutEvaluationCut_realizes_iff]
    exact hG
  simpa only [cut_cutEvaluationCut] using
    sum_isPrefix_of_sub_realizes (cutEvaluationCut F) (cutEvaluationCut G) z hc hd

end

end Surreal.Foundations.SmallNormalForm
