import Surreal.Foundations.SmallNormalFormTruncation
import Surreal.Foundations.SignSequenceValuationBalls
import Surreal.Foundations.SignSequenceValuationApproximation

/-!
# A canonical cut candidate for every small formal normal form

Recursion on the lower-universe ordinal support length assigns an actual
sign sequence to each small formal form. At every exponent, the value
agrees to strictly higher valuation with the recursively evaluated earlier
truncation plus that exponent's term. Pairwise compatibility of these
approximations is proved by length induction, so the defining cut exists.

The result is the simplest simultaneous solution of these recursive bounds.
This constructs a candidate, not an arithmetic homomorphism or an inverse
normal-form theorem. Those conclusions require further compatibility and
termination arguments.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence
open scoped Classical

noncomputable section

private abbrev LengthLT (F G : SmallNormalForm.{u}) : Prop := length F < length G

private theorem lengthLT_wf : WellFounded (LengthLT : SmallNormalForm.{u} → _ → Prop) :=
  InvImage.wf length Ordinal.lt_wf

/-- The fallback only totalizes the recursive definition. The compatibility
proof below shows that it is never used. -/
private def cutEvaluationStep (F : SmallNormalForm.{u})
    (f : ∀ G : SmallNormalForm.{u}, LengthLT G F → SignSequence.{u}) : SignSequence.{u} :=
  let c : support F → SignSequence.{u} := fun a =>
    f (trunc F a.val) (length_trunc_lt F a.property) + ofReal (coeff F a.val) * omegaPower a.val
  let t : support F → SignSequence.{u} := fun a => -a.val
  if h : ∀ a b, ((min (t a) (t b) : SignSequence.{u}) : WithTop SignSequence.{u}) <
      valuation (c a - c b) then
    simplestValuationBallPoint c t h
  else 0

/-- The actual sign-sequence candidate obtained recursively from the formal support. -/
def cutEvaluation : SmallNormalForm.{u} → SignSequence.{u} :=
  lengthLT_wf.fix cutEvaluationStep

private theorem cutEvaluation_unfold (F : SmallNormalForm.{u}) :
    cutEvaluation F = cutEvaluationStep F (fun G _ => cutEvaluation G) :=
  lengthLT_wf.fix_eq cutEvaluationStep F

/-- The recursive partial value through one specified growth exponent. -/
def cutEvaluationCenter (F : SmallNormalForm.{u}) (a : SignSequence.{u}) : SignSequence.{u} :=
  cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a

private def CentersCompatible (F : SmallNormalForm.{u}) : Prop :=
  ∀ a b : support F,
    ((min (-a.val) (-b.val) : SignSequence.{u}) : WithTop SignSequence.{u}) <
      valuation (cutEvaluationCenter F a.val - cutEvaluationCenter F b.val)

private theorem cutEvaluation_eq_of_compatible (F : SmallNormalForm.{u}) (h : CentersCompatible F) :
    cutEvaluation F = simplestValuationBallPoint
      (fun a : support F => cutEvaluationCenter F a.val) (fun a : support F => -a.val) h := by
  rw [cutEvaluation_unfold]
  unfold cutEvaluationStep
  change (if h : CentersCompatible F then _ else 0) = _
  rw [dif_pos h]
  rfl

private theorem cutEvaluation_remainder_of_compatible (F : SmallNormalForm.{u})
    (h : CentersCompatible F) (a : support F) :
    (-a.val : WithTop SignSequence.{u}) <
      valuation (cutEvaluation F - cutEvaluationCenter F a.val) := by
  rw [cutEvaluation_eq_of_compatible F h]
  exact simplestValuationBallPoint_mem _ _ h a

/-- All recursive centers are compatible; no compatibility assumption is
required of the input formal normal form. -/
private theorem cutEvaluation_compatible (F : SmallNormalForm.{u}) : CentersCompatible F := by
  induction F using lengthLT_wf.induction with
  | h F ih =>
    have hpair (a b : support F) (hba : b.val < a.val) :
        (-a.val : WithTop SignSequence.{u}) <
          valuation (cutEvaluationCenter F b.val - cutEvaluationCenter F a.val) := by
      have ham : a.val ∈ support (trunc F b.val) := by
        rw [support_trunc]
        exact ⟨a.property, hba⟩
      have hsmall := ih (trunc F b.val) (length_trunc_lt F b.property)
      have hr := cutEvaluation_remainder_of_compatible (trunc F b.val) hsmall ⟨a.val, ham⟩
      have hc : cutEvaluationCenter (trunc F b.val) a.val = cutEvaluationCenter F a.val := by
        unfold cutEvaluationCenter
        rw [trunc_trunc, max_eq_right hba.le, coeff_trunc_of_lt F hba]
      rw [hc] at hr
      have ht : (-a.val : WithTop SignSequence.{u}) <
          valuation (ofReal (coeff F b.val) * omegaPower b.val) := by
        rw [valuation_monomial_of_mem_support F b.property]
        exact WithTop.coe_lt_coe.mpr (neg_lt_neg hba)
      have hv := (lt_min hr ht).trans_le
        (min_valuation_le_add
          (cutEvaluation (trunc F b.val) - cutEvaluationCenter F a.val)
          (ofReal (coeff F b.val) * omegaPower b.val))
      convert hv using 1
      congr 1
      unfold cutEvaluationCenter
      abel
    intro a b
    rcases lt_trichotomy a.val b.val with hab | hab | hba
    · have hm : min (-a.val) (-b.val) = -b.val := min_eq_right (neg_le_neg hab.le)
      rw [hm]
      exact hpair b a hab
    · have he : a = b := Subtype.ext hab
      subst b
      simp only [min_self, sub_self, valuation_zero, WithTop.coe_lt_top]
    · have hm : min (-a.val) (-b.val) = -a.val := min_eq_left (neg_le_neg hba.le)
      rw [hm, valuation_sub_comm]
      exact hpair a b hba

/-- The recursive centers satisfy the pairwise bound required by the small-cut theorem. -/
theorem cutEvaluation_centers_compatible (F : SmallNormalForm.{u})
    (a b : support F) :
    ((min (-a.val) (-b.val) : SignSequence.{u}) : WithTop SignSequence.{u}) <
      valuation (cutEvaluationCenter F a.val - cutEvaluationCenter F b.val) :=
  cutEvaluation_compatible F a b

/-- The guarded recursion always takes its canonical-cut branch. -/
theorem cutEvaluation_eq_simplest (F : SmallNormalForm.{u}) :
    cutEvaluation F = simplestValuationBallPoint
      (fun a : support F => cutEvaluationCenter F a.val) (fun a : support F => -a.val)
      (cutEvaluation_centers_compatible F) :=
  cutEvaluation_eq_of_compatible F (cutEvaluation_compatible F)

/-- Every exponent has a strictly higher-valuation remainder after its
recursively evaluated earlier terms and its own monomial term. -/
theorem cutEvaluation_remainder (F : SmallNormalForm.{u}) (a : SignSequence.{u})
    (ha : a ∈ support F) :
    (-a : WithTop SignSequence.{u}) < valuation
      (cutEvaluation F - (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a)) :=
  cutEvaluation_remainder_of_compatible F (cutEvaluation_compatible F) ⟨a, ha⟩

/-- The constructed candidate is a prefix of every simultaneous solution
of its recursive truncation bounds. -/
theorem cutEvaluation_isPrefix (F : SmallNormalForm.{u}) (x : SignSequence.{u})
    (hx : ∀ a ∈ support F, (-a : WithTop SignSequence.{u}) <
      valuation (x - (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a))) :
    IsPrefix (cutEvaluation F) x := by
  rw [cutEvaluation_eq_simplest]
  exact simplestValuationBallPoint_isPrefix _ _ _ x (fun a => hx a.val a.property)

/-- The recursive residual constraints uniquely specify their simplest
solution, with no claim that all solutions coincide. -/
theorem existsUnique_simplest_cutEvaluation (F : SmallNormalForm.{u}) :
    ∃! x : SignSequence.{u},
      (∀ a ∈ support F, (-a : WithTop SignSequence.{u}) <
        valuation (x - (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a))) ∧
      ∀ y : SignSequence.{u},
        (∀ a ∈ support F, (-a : WithTop SignSequence.{u}) <
          valuation (y - (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a))) →
        IsPrefix x y := by
  refine ⟨cutEvaluation F, ⟨cutEvaluation_remainder F, cutEvaluation_isPrefix F⟩, ?_⟩
  intro y hy
  exact IsPrefix.antisymm (hy.2 _ (cutEvaluation_remainder F))
    (cutEvaluation_isPrefix F y hy.1)

/-- The empty formal support evaluates to the empty sign sequence. -/
@[simp] theorem cutEvaluation_zero : cutEvaluation (0 : SmallNormalForm.{u}) = 0 := by
  apply IsPrefix.antisymm (cutEvaluation_isPrefix 0 0 ?_)
  · exact ⟨by simp, fun i hi => by simp at hi⟩
  · intro a ha
    simp at ha

end

end Surreal.Foundations.SmallNormalForm
