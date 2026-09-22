import Surreal.Foundations.SmallNormalFormEvaluation

/-!
# Negation of canonical small normal-form values

Negating coefficients preserves the formal support and commutes with every
truncation. Length induction then identifies the recursive centers for the
negative form. Negation preserves both valuation bounds and the prefix
relation, so the two simplest solutions are negatives of one another.

The argument uses prefix simplicity, not uniqueness of valuation
approximations. It applies to arbitrary small supports.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

@[simp] theorem coeff_neg (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    coeff (-F) a = -coeff F a := rfl

@[simp] theorem support_neg (F : SmallNormalForm.{u}) : support (-F) = support F := by
  ext a
  simp only [mem_support, coeff_neg, neg_ne_zero]

@[simp] theorem length_neg (F : SmallNormalForm.{u}) : length (-F) = length F := by
  have hs : _root_.SurrealHahnSeries.support (-F) = _root_.SurrealHahnSeries.support F := by
    ext a
    simp only [_root_.SurrealHahnSeries.mem_support_iff,
      _root_.SurrealHahnSeries.coeff_neg, Pi.neg_apply, neg_ne_zero]
  exact le_antisymm (_root_.SurrealHahnSeries.length_mono hs.subset)
    (_root_.SurrealHahnSeries.length_mono hs.superset)

@[simp] theorem trunc_neg (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    trunc (-F) a = -trunc F a := by
  apply ext
  intro b
  simp only [coeff_trunc, coeff_neg]
  split <;> simp_all

/-- Negating all formal coefficients negates the canonical simplest value. -/
@[simp] theorem cutEvaluation_neg (F : SmallNormalForm.{u}) :
    cutEvaluation (-F) = -cutEvaluation F := by
  induction F using (InvImage.wf length Ordinal.lt_wf).induction with
  | h F ih =>
    have hc (a : SignSequence.{u}) (ha : a ∈ support F) :
        cutEvaluationCenter (-F) a = -cutEvaluationCenter F a := by
      unfold cutEvaluationCenter
      rw [trunc_neg, ih (trunc F a) (length_trunc_lt F ha), coeff_neg, map_neg, neg_mul]
      abel
    have hp : IsPrefix (cutEvaluation (-F)) (-cutEvaluation F) := by
      apply cutEvaluation_isPrefix
      intro a ha
      have ha' : a ∈ support F := by simpa only [support_neg] using ha
      change (-a : WithTop SignSequence.{u}) <
        valuation (-cutEvaluation F - cutEvaluationCenter (-F) a)
      rw [hc a ha']
      rw [show -cutEvaluation F - -cutEvaluationCenter F a =
        -(cutEvaluation F - cutEvaluationCenter F a) by abel, valuation_neg]
      exact cutEvaluation_remainder F a ha'
    have hq : IsPrefix (cutEvaluation F) (-cutEvaluation (-F)) := by
      apply cutEvaluation_isPrefix
      intro a ha
      have ha' : a ∈ support (-F) := by simpa only [support_neg] using ha
      have hr := cutEvaluation_remainder (-F) a ha'
      change (-a : WithTop SignSequence.{u}) <
        valuation (cutEvaluation (-F) - cutEvaluationCenter (-F) a) at hr
      rw [hc a ha] at hr
      change (-a : WithTop SignSequence.{u}) <
        valuation (-cutEvaluation (-F) - cutEvaluationCenter F a)
      rw [show -cutEvaluation (-F) - cutEvaluationCenter F a =
        -(cutEvaluation (-F) - -cutEvaluationCenter F a) by abel, valuation_neg]
      exact hr
    exact hp.antisymm (by simpa only [neg_neg] using hq.neg)

/-- Recursive partial values commute with coefficient negation as well. -/
@[simp] theorem cutEvaluationCenter_neg (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    cutEvaluationCenter (-F) a = -cutEvaluationCenter F a := by
  unfold cutEvaluationCenter
  rw [trunc_neg, cutEvaluation_neg, coeff_neg, map_neg, neg_mul]
  abel

end

end Surreal.Foundations.SmallNormalForm
