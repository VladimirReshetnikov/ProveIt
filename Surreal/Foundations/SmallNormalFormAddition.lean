import Surreal.Foundations.SmallNormalFormInitialEvaluation
import Surreal.Foundations.SmallNormalFormSumSimplicity

/-!
# Addition of canonical small normal-form values

Induction on both support lengths proves addition compatibility. The actual
sum satisfies the formal sum's recursive centers. Conversely, comparison
with each translated truncation shows that the formal sum's value realizes
the Conway sum cut. The two prefix comparisons identify these values;
valuation approximations alone are never used as a uniqueness principle.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

@[simp] theorem trunc_add (F G : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    trunc (F + G) a = trunc F a + trunc G a := by
  apply ext
  intro b
  simp only [coeff_trunc, coeff_add]
  split <;> simp_all

/-- Equal earlier formal parts cancel in actual evaluation up to strictly
higher valuation than the coefficient difference at the cutoff. -/
theorem cutEvaluation_sub_residual_of_trunc_eq {F G : SmallNormalForm.{u}}
    {a : SignSequence.{u}} (ht : trunc F a = trunc G a) :
    (-a : WithTop SignSequence.{u}) < valuation
      ((cutEvaluation F - cutEvaluation G) -
        ofReal (coeff F a - coeff G a) * omegaPower a) := by
  have hF := cutEvaluation_remainder_all F a
  have hG := cutEvaluation_remainder_all G a
  rw [← ht] at hG
  have hv := min_valuation_le_add
    (cutEvaluation F - (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a))
    (-(cutEvaluation G - (cutEvaluation (trunc F a) + ofReal (coeff G a) * omegaPower a)))
  rw [valuation_neg] at hv
  have hr := (lt_min hF hG).trans_le hv
  convert hr using 1
  congr 1
  rw [map_sub, sub_mul]
  abel

/-- The inductively known sums of earlier parts supply all center bounds
for the sum of two actual candidates. -/
private theorem approximates_add_of_trunc_add (F G : SmallNormalForm.{u})
    (h : ∀ a ∈ support (F + G),
      cutEvaluation (trunc F a + trunc G a) =
        cutEvaluation (trunc F a) + cutEvaluation (trunc G a)) :
    Approximates (F + G) (cutEvaluation F + cutEvaluation G) := by
  intro a ha
  have hF := cutEvaluation_remainder_all F a
  have hG := cutEvaluation_remainder_all G a
  have hr := (lt_min hF hG).trans_le (min_valuation_le_add
    (cutEvaluation F - (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a))
    (cutEvaluation G - (cutEvaluation (trunc G a) + ofReal (coeff G a) * omegaPower a)))
  change (-a : WithTop SignSequence.{u}) < valuation
    ((cutEvaluation F + cutEvaluation G) -
      (cutEvaluation (trunc (F + G) a) + ofReal (coeff (F + G) a) * omegaPower a))
  rw [trunc_add, h a ha, coeff_add, map_add, add_mul]
  convert hr using 1
  congr 1
  abel

/-- Translating the first summand's centers uses only sums involving its
strict earlier truncations. -/
private theorem approximates_sub_right_of_trunc_add (F G : SmallNormalForm.{u})
    (h : ∀ a ∈ support F,
      cutEvaluation (trunc F a + G) = cutEvaluation (trunc F a) + cutEvaluation G) :
    Approximates F (cutEvaluation (F + G) - cutEvaluation G) := by
  intro a ha
  have ht : trunc (F + G) a = trunc (trunc F a + G) a := by
    rw [trunc_add, trunc_add, trunc_trunc, max_self]
  have hc : coeff (F + G) a - coeff (trunc F a + G) a = coeff F a := by
    simp [coeff_add]
  have hr := cutEvaluation_sub_residual_of_trunc_eq ht
  rw [hc, h a ha] at hr
  change (-a : WithTop SignSequence.{u}) < valuation
    ((cutEvaluation (F + G) - cutEvaluation G) -
      (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a))
  convert hr using 1
  congr 1
  abel

/-- Canonical evaluation preserves addition on arbitrary small supports. -/
@[simp] theorem cutEvaluation_add (F G : SmallNormalForm.{u}) :
    cutEvaluation (F + G) = cutEvaluation F + cutEvaluation G := by
  induction F using (InvImage.wf length Ordinal.lt_wf).induction generalizing G with
  | h F ihF =>
    induction G using (InvImage.wf length Ordinal.lt_wf).induction with
    | h G ihG =>
      apply IsPrefix.antisymm
      · apply (approximates_add_of_trunc_add F G ?_).isPrefix
        intro a ha
        by_cases he : trunc F a = F
        · have hFa : coeff F a = 0 := by
            rw [← he]
            exact coeff_trunc_of_le F le_rfl
          have hGa : a ∈ support G := by
            simpa only [mem_support, coeff_add, hFa, _root_.zero_add] using ha
          simpa only [he] using ihG (trunc G a) (length_trunc_lt G hGa)
        · exact ihF (trunc F a) ((trunc_isInitialSegment F a).length_lt he) (trunc G a)
      · apply cutEvaluation_add_isPrefix_of_approximates F G (cutEvaluation (F + G))
        · exact approximates_sub_right_of_trunc_add F G
            (fun a ha => ihF (trunc F a) (length_trunc_lt F ha) G)
        · have hg := approximates_sub_right_of_trunc_add G F (fun a ha => by
            rw [_root_.add_comm (trunc G a) F, ihG (trunc G a) (length_trunc_lt G ha),
              _root_.add_comm (cutEvaluation F) (cutEvaluation (trunc G a))])
          simpa only [_root_.add_comm G F] using hg

end

end Surreal.Foundations.SmallNormalForm
