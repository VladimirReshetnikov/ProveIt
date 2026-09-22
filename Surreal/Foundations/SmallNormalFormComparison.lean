import Surreal.Foundations.SmallNormalFormLeading
import Surreal.Foundations.SmallNormalFormCutTruncation

/-!
# Comparing canonical small normal-form candidates

The greatest exponent at which two formal forms differ determines the
leading data of the difference of their actual cut candidates. This gives
injectivity and a strict order embedding on arbitrary small supports.
No assertion that evaluation preserves addition or multiplication is used.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

@[simp] theorem trunc_sub (F G : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    trunc (F - G) a = trunc F a - trunc G a := by
  apply ext
  intro b
  simp only [coeff_trunc, coeff_sub]
  split <;> simp_all

/-- The formal initial portions agree above the first differing exponent. -/
theorem trunc_eq_at_first_difference (F G : SmallNormalForm.{u})
    (h : 0 < length (F - G)) :
    trunc F (exponent (F - G) ⟨0, h⟩) = trunc G (exponent (F - G) ⟨0, h⟩) := by
  apply sub_eq_zero.mp
  rw [← trunc_sub, trunc_exponent_zero]

/-- The first formal difference determines the leading data of the actual
candidate difference, without assuming evaluation is additive. -/
theorem leading_cutEvaluation_sub (F G : SmallNormalForm.{u})
    (h : 0 < length (F - G)) :
    SignSequence.leadingExponent (cutEvaluation F - cutEvaluation G) = exponent (F - G) ⟨0, h⟩ ∧
      SignSequence.leadingCoeff (cutEvaluation F - cutEvaluation G) = coefficientAt (F - G) 0 := by
  let a := exponent (F - G) ⟨0, h⟩
  have ht : trunc F a = trunc G a := trunc_eq_at_first_difference F G h
  have hF := cutEvaluation_remainder_all F a
  have hG := cutEvaluation_remainder_all G a
  rw [← ht] at hG
  have hr : (-a : WithTop SignSequence.{u}) < valuation
      ((cutEvaluation F - (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a)) -
        (cutEvaluation G - (cutEvaluation (trunc F a) + ofReal (coeff G a) * omegaPower a))) := by
    have hv := min_valuation_le_add
      (cutEvaluation F - (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a))
      (-(cutEvaluation G - (cutEvaluation (trunc F a) + ofReal (coeff G a) * omegaPower a)))
    rw [valuation_neg] at hv
    simpa only [sub_eq_add_neg] using (lt_min hF hG).trans_le hv
  have hb : (-a : WithTop SignSequence.{u}) < valuation
      ((cutEvaluation F - cutEvaluation G) - ofReal (coeff (F - G) a) * omegaPower a) := by
    convert hr using 1
    congr 1
    rw [coeff_sub, map_sub, sub_mul]
    abel
  have hc : coeff (F - G) a ≠ 0 := exponent_mem_support (F - G) ⟨0, h⟩
  have hl := leading_of_valuation_sub_omega_gt _ a _ hc hb
  exact ⟨hl.1, hl.2.trans (coeff_exponent (F - G) ⟨0, h⟩)⟩

/-- Distinct small formal forms give distinct actual surreal candidates. -/
theorem cutEvaluation_injective : Function.Injective (cutEvaluation : SmallNormalForm.{u} → _) := by
  intro F G he
  by_contra hne
  have h : 0 < length (F - G) := bot_lt_iff_ne_bot.mpr
    ((length_eq_zero (F - G)).not.mpr (sub_ne_zero.mpr hne))
  have hc := (leading_cutEvaluation_sub F G h).2
  rw [he, sub_self, SignSequence.leadingCoeff_zero] at hc
  exact ((coefficientAt_eq_zero (F - G) 0).not.mpr (not_le_of_gt h)) hc.symm

/-- Actual differences and formal differences have the same leading coefficient. -/
theorem leadingCoeff_cutEvaluation_sub (F G : SmallNormalForm.{u}) :
    SignSequence.leadingCoeff (cutEvaluation F - cutEvaluation G) = (ofLex (F - G).val).leadingCoeff := by
  by_cases he : F = G
  · subst G
    simp only [sub_self, SignSequence.leadingCoeff_zero]
    exact _root_.HahnSeries.leadingCoeff_zero.symm
  have h : 0 < length (F - G) := bot_lt_iff_ne_bot.mpr
    ((length_eq_zero (F - G)).not.mpr (sub_ne_zero.mpr he))
  rw [(leading_cutEvaluation_sub F G h).2, hahn_leadingCoeff_eq_coefficientAt (F - G) h]

/-- Numerical comparison is exactly the formal lexicographic comparison. -/
@[simp] theorem cutEvaluation_lt_iff (F G : SmallNormalForm.{u}) :
    cutEvaluation F < cutEvaluation G ↔ F < G := by
  rw [← sub_pos, ← SignSequence.leadingCoeff_pos_iff, leadingCoeff_cutEvaluation_sub]
  exact (_root_.HahnSeries.leadingCoeff_pos_iff (x := (G - F).val)).trans
    (_root_.sub_pos : 0 < G - F ↔ F < G)

@[simp] theorem cutEvaluation_le_iff (F G : SmallNormalForm.{u}) :
    cutEvaluation F ≤ cutEvaluation G ↔ F ≤ G := by
  rw [← not_lt, ← not_lt, cutEvaluation_lt_iff]

/-- The canonical cut candidates form a strict order embedding. -/
def cutEvaluationOrderEmbedding : SmallNormalForm.{u} ↪o SignSequence.{u} where
  toFun := cutEvaluation
  inj' := cutEvaluation_injective
  map_rel_iff' := cutEvaluation_le_iff _ _

/-- Distances measured by the actual valuation agree with the valuation of
the candidate for the formal difference. This does not identify the values. -/
theorem valuation_cutEvaluation_sub (F G : SmallNormalForm.{u}) :
    valuation (cutEvaluation F - cutEvaluation G) = valuation (cutEvaluation (F - G)) := by
  by_cases he : F = G
  · subst G
    simp
  have h : 0 < length (F - G) := bot_lt_iff_ne_bot.mpr
    ((length_eq_zero (F - G)).not.mpr (sub_ne_zero.mpr he))
  rw [valuation_of_ne_zero (sub_ne_zero.mpr (cutEvaluation_injective.ne he)),
    (leading_cutEvaluation_sub F G h).1, valuation_cutEvaluation (F - G) h]

end

end Surreal.Foundations.SmallNormalForm
