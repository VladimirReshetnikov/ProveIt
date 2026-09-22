import Surreal.Foundations.SmallNormalFormAddEquiv
import Surreal.Foundations.SmallNormalFormProductFrontier
import Surreal.Foundations.SignSequenceProductCuts
import Surreal.Foundations.SignSequenceRecursion

/-!
# Multiplication of canonical small normal-form values

The two simplicity comparisons use induction on the birthdays of the two
actual factors. Canonical Conway product options give one comparison. For
the other, a supported product exponent is split into two supported factor
exponents: products involving strict earlier truncations are already known,
and the remaining rectangle has a known leading monomial. The resulting
center bounds give a prefix comparison, rather than an unjustified claim
that valuation approximation alone determines the product uniquely.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

private theorem birthday_cutEvaluation_trunc_lt (F : SmallNormalForm.{u})
    {a : SignSequence.{u}} (ha : a ∈ support F) :
    (cutEvaluation (trunc F a)).birthday < (cutEvaluation F).birthday := by
  have hp := cutEvaluation_trunc_isPrefix F a
  have hn : cutEvaluation (trunc F a) ≠ cutEvaluation F := by
    apply cutEvaluation_injective.ne
    intro he
    exact (length_trunc_lt F ha).ne (congrArg length he)
  apply lt_of_le_of_ne hp.1
  intro he
  apply hn
  apply hp.antisymm
  exact ⟨he.ge, fun i hi => (hp.2 i (by simpa only [he] using hi)).symm⟩

private theorem tail_product_remainder (F G : SmallNormalForm.{u})
    {a b : SignSequence.{u}} (ha : a ∈ support F) (hb : b ∈ support G) :
    (-(a + b) : WithTop SignSequence.{u}) < valuation
      ((cutEvaluation F - cutEvaluation (trunc F a)) *
        (cutEvaluation G - cutEvaluation (trunc G b)) -
        ofReal (coeff F a * coeff G b) * omegaPower (a + b)) := by
  have hf := cutEvaluation_remainder F a ha
  have hg := cutEvaluation_remainder G b hb
  have hfl : leadingExponent (cutEvaluation F - cutEvaluation (trunc F a)) = a ∧
      SignSequence.leadingCoeff (cutEvaluation F - cutEvaluation (trunc F a)) = coeff F a := by
    apply leading_of_valuation_sub_omega_gt _ a _ ha
    convert hf using 1
    congr 1
    abel_nf
  have hgl : leadingExponent (cutEvaluation G - cutEvaluation (trunc G b)) = b ∧
      SignSequence.leadingCoeff (cutEvaluation G - cutEvaluation (trunc G b)) = coeff G b := by
    apply leading_of_valuation_sub_omega_gt _ b _ hb
    convert hg using 1
    congr 1
    abel_nf
  have hfn : cutEvaluation F - cutEvaluation (trunc F a) ≠ 0 := by
    intro he
    have hc := hfl.2
    rw [he, SignSequence.leadingCoeff_zero] at hc
    exact ha hc.symm
  have hgn : cutEvaluation G - cutEvaluation (trunc G b) ≠ 0 := by
    intro he
    have hc := hgl.2
    rw [he, SignSequence.leadingCoeff_zero] at hc
    exact hb hc.symm
  apply (valuation_sub_omega_gt_iff _ _ _ (mul_ne_zero ha hb)).mpr
  constructor
  · rw [leadingExponent_mul hfn hgn, hfl.1, hgl.1]
  · rw [SignSequence.leadingCoeff_mul, hfl.2, hgl.2]

private theorem product_remainder_of_frontier (F G : SmallNormalForm.{u})
    {a b : SignSequence.{u}} (ha : a ∈ support F) (hb : b ∈ support G)
    (hA : cutEvaluation (trunc F a * G) = cutEvaluation (trunc F a) * cutEvaluation G)
    (hB : cutEvaluation (F * trunc G b) = cutEvaluation F * cutEvaluation (trunc G b))
    (hAB : cutEvaluation (trunc F a * trunc G b) =
      cutEvaluation (trunc F a) * cutEvaluation (trunc G b))
    (ht : trunc (F * G) (a + b) =
      trunc (trunc F a * G + F * trunc G b - trunc F a * trunc G b) (a + b))
    (hc : coeff (F * G) (a + b) =
      coeff (trunc F a * G + F * trunc G b - trunc F a * trunc G b) (a + b) +
        coeff F a * coeff G b) :
    (-(a + b) : WithTop SignSequence.{u}) < valuation
      (cutEvaluation F * cutEvaluation G -
        (cutEvaluation (trunc (F * G) (a + b)) +
          ofReal (coeff (F * G) (a + b)) * omegaPower (a + b))) := by
  let H := trunc F a * G + F * trunc G b - trunc F a * trunc G b
  have hH : cutEvaluation H = cutEvaluation (trunc F a) * cutEvaluation G +
      cutEvaluation F * cutEvaluation (trunc G b) -
        cutEvaluation (trunc F a) * cutEvaluation (trunc G b) := by
    simp only [H, cutEvaluation_sub, cutEvaluation_add, hA, hB, hAB]
  have hr := (lt_min (cutEvaluation_remainder_all H (a + b))
      (tail_product_remainder F G ha hb)).trans_le (min_valuation_le_add
    (cutEvaluation H - (cutEvaluation (trunc H (a + b)) +
      ofReal (coeff H (a + b)) * omegaPower (a + b)))
    ((cutEvaluation F - cutEvaluation (trunc F a)) *
      (cutEvaluation G - cutEvaluation (trunc G b)) -
      ofReal (coeff F a * coeff G b) * omegaPower (a + b)))
  have he : cutEvaluation F * cutEvaluation G -
      (cutEvaluation (trunc (F * G) (a + b)) +
        ofReal (coeff (F * G) (a + b)) * omegaPower (a + b)) =
      (cutEvaluation H - (cutEvaluation (trunc H (a + b)) +
        ofReal (coeff H (a + b)) * omegaPower (a + b))) +
      ((cutEvaluation F - cutEvaluation (trunc F a)) *
        (cutEvaluation G - cutEvaluation (trunc G b)) -
        ofReal (coeff F a * coeff G b) * omegaPower (a + b)) := by
    rw [ht, hc, map_add, add_mul, hH]
    dsimp only [H]
    ring
  rw [he]
  exact hr

private theorem mul_isPrefix_of_smaller_mul (F G : SmallNormalForm.{u})
    (hF : ∀ A : SmallNormalForm.{u},
      (cutEvaluation A).birthday < (cutEvaluation F).birthday →
      ∀ B, cutEvaluation (A * B) = cutEvaluation A * cutEvaluation B)
    (hG : ∀ B : SmallNormalForm.{u},
      (cutEvaluation B).birthday < (cutEvaluation G).birthday →
      cutEvaluation (F * B) = cutEvaluation F * cutEvaluation B) :
    IsPrefix (cutEvaluation F * cutEvaluation G) (cutEvaluation (F * G)) := by
  have hrect (a b : SignSequence.{u})
      (ha : a.birthday < (cutEvaluation F).birthday)
      (hb : b.birthday < (cutEvaluation G).birthday) :
      mulOption (cutEvaluation F) (cutEvaluation G) a b =
        cutEvaluation (normalForm a * G + F * normalForm b - normalForm a * normalForm b) := by
    have ha' : (cutEvaluation (normalForm a)).birthday < (cutEvaluation F).birthday := by
      simpa only [cutEvaluation_normalForm] using ha
    have hb' : (cutEvaluation (normalForm b)).birthday < (cutEvaluation G).birthday := by
      simpa only [cutEvaluation_normalForm] using hb
    simp only [sub_eq_add_neg, cutEvaluation_add, cutEvaluation_neg, hF _ ha', hG _ hb',
      cutEvaluation_normalForm, mulOption]
  have hdiff (A B : SmallNormalForm.{u}) :
      F * G - (A * G + F * B - A * B) = (F - A) * (G - B) := by ring
  rw [mul_eq_cut]
  apply cut_isPrefix
  constructor
  · intro i
    change mulLeft (cutEvaluation F) (cutEvaluation G) ((equivShrink _).symm i) < _
    rcases (equivShrink _).symm i with ⟨i, j⟩ | ⟨i, j⟩
    · change mulOption _ _ _ _ < _
      rw [hrect _ _ (leftOption_simpler _ i).2 (leftOption_simpler _ j).2,
        cutEvaluation_lt_iff, ← sub_pos, hdiff]
      apply mul_pos
      · apply sub_pos.mpr
        apply (cutEvaluation_lt_iff _ _).mp
        simpa only [cutEvaluation_normalForm] using leftOption_lt (cutEvaluation F) i
      · apply sub_pos.mpr
        apply (cutEvaluation_lt_iff _ _).mp
        simpa only [cutEvaluation_normalForm] using leftOption_lt (cutEvaluation G) j
    · change mulOption _ _ _ _ < _
      rw [hrect _ _ (rightOption_simpler _ i).2 (rightOption_simpler _ j).2,
        cutEvaluation_lt_iff, ← sub_pos, hdiff]
      apply mul_pos_of_neg_of_neg
      · apply sub_neg.mpr
        apply (cutEvaluation_lt_iff _ _).mp
        simpa only [cutEvaluation_normalForm] using lt_rightOption (cutEvaluation F) i
      · apply sub_neg.mpr
        apply (cutEvaluation_lt_iff _ _).mp
        simpa only [cutEvaluation_normalForm] using lt_rightOption (cutEvaluation G) j
  · intro i
    change _ < mulRight (cutEvaluation F) (cutEvaluation G) ((equivShrink _).symm i)
    rcases (equivShrink _).symm i with ⟨i, j⟩ | ⟨i, j⟩
    · change _ < mulOption _ _ _ _
      rw [hrect _ _ (leftOption_simpler _ i).2 (rightOption_simpler _ j).2,
        cutEvaluation_lt_iff, ← sub_neg, hdiff]
      apply mul_neg_of_pos_of_neg
      · apply sub_pos.mpr
        apply (cutEvaluation_lt_iff _ _).mp
        simpa only [cutEvaluation_normalForm] using leftOption_lt (cutEvaluation F) i
      · apply sub_neg.mpr
        apply (cutEvaluation_lt_iff _ _).mp
        simpa only [cutEvaluation_normalForm] using lt_rightOption (cutEvaluation G) j
    · change _ < mulOption _ _ _ _
      rw [hrect _ _ (rightOption_simpler _ i).2 (leftOption_simpler _ j).2,
        cutEvaluation_lt_iff, ← sub_neg, hdiff]
      apply mul_neg_of_neg_of_pos
      · apply sub_neg.mpr
        apply (cutEvaluation_lt_iff _ _).mp
        simpa only [cutEvaluation_normalForm] using lt_rightOption (cutEvaluation F) i
      · apply sub_pos.mpr
        apply (cutEvaluation_lt_iff _ _).mp
        simpa only [cutEvaluation_normalForm] using leftOption_lt (cutEvaluation G) j

/-- Canonical evaluation preserves multiplication on arbitrary small supports. -/
@[simp] theorem cutEvaluation_mul (F G : SmallNormalForm.{u}) :
    cutEvaluation (F * G) = cutEvaluation F * cutEvaluation G := by
  induction F using (InvImage.wf
      (fun H : SmallNormalForm.{u} => (cutEvaluation H).birthday) Ordinal.lt_wf).induction
      generalizing G with
  | h F ihF =>
    induction G using (InvImage.wf
        (fun H : SmallNormalForm.{u} => (cutEvaluation H).birthday) Ordinal.lt_wf).induction with
    | h G ihG =>
      apply IsPrefix.antisymm
      · apply cutEvaluation_isPrefix
        intro c hc
        obtain ⟨a, ha, b, hb, rfl⟩ := exists_add_eq_of_mem_support_mul F G hc
        have hFa := birthday_cutEvaluation_trunc_lt F ha
        have hGb := birthday_cutEvaluation_trunc_lt G hb
        exact product_remainder_of_frontier F G ha hb
          (ihF (trunc F a) hFa G) (ihG (trunc G b) hGb)
          (ihF (trunc F a) hFa (trunc G b))
          (trunc_product_frontier F G a b) (coeff_product_frontier F G ha hb)
      · exact mul_isPrefix_of_smaller_mul F G ihF ihG

end

end Surreal.Foundations.SmallNormalForm
