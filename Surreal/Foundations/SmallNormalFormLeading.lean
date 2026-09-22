import Surreal.Foundations.SmallNormalFormEvaluation
import Surreal.Foundations.SignSequenceLeadingTerm

/-!
# Leading data of the canonical cut candidate

The first formal exponent has empty earlier truncation. The proved residual
bound therefore identifies the actual leading exponent and coefficient of
the cut candidate. In particular a nonzero formal form has a nonzero
candidate. Actual and native formal leading coefficients agree, so
positivity and nonnegativity are preserved and reflected, including zero.
This does not assert a full order embedding, injectivity between two nonzero
forms, or preservation of sums and products.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

noncomputable section

/-- The first formal term gives the actual leading data of the candidate. -/
theorem leading_cutEvaluation (F : SmallNormalForm.{u}) (hF : 0 < length F) :
    SignSequence.leadingExponent (cutEvaluation F) = exponent F ⟨0, hF⟩ ∧
      SignSequence.leadingCoeff (cutEvaluation F) = coefficientAt F 0 := by
  have h := cutEvaluation_remainder F (exponent F ⟨0, hF⟩)
    (exponent_mem_support F ⟨0, hF⟩)
  simp only [trunc_exponent_zero, cutEvaluation_zero, SignSequence.zero_add, coeff_exponent] at h
  exact SignSequence.leading_of_valuation_sub_omega_gt _ _ _
    ((coefficientAt_eq_zero F 0).not.mpr (not_le_of_gt hF)) h

/-- A nonzero formal normal form has a nonzero actual cut candidate. -/
theorem cutEvaluation_ne_zero {F : SmallNormalForm.{u}} (hF : F ≠ 0) : cutEvaluation F ≠ 0 := by
  have hlen : 0 < length F := bot_lt_iff_ne_bot.mpr ((length_eq_zero F).not.mpr hF)
  have hc := (leading_cutEvaluation F hlen).2
  intro hz
  rw [hz, SignSequence.leadingCoeff_zero] at hc
  exact ((coefficientAt_eq_zero F 0).not.mpr (not_le_of_gt hlen)) hc.symm

@[simp] theorem cutEvaluation_eq_zero_iff (F : SmallNormalForm.{u}) :
    cutEvaluation F = 0 ↔ F = 0 :=
  ⟨fun h => by by_contra hF; exact cutEvaluation_ne_zero hF h,
    fun h => by simp [h]⟩

/-- The candidate's valuation is the negative first growth exponent. -/
theorem valuation_cutEvaluation (F : SmallNormalForm.{u}) (hF : 0 < length F) :
    SignSequence.valuation (cutEvaluation F) =
      ((-exponent F ⟨0, hF⟩ : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  rw [SignSequence.valuation_of_ne_zero
    (cutEvaluation_ne_zero ((length_eq_zero F).not.mp (ne_of_gt hF))),
    (leading_cutEvaluation F hF).1]

/-- Positivity is decided by the first nonzero coefficient of the formal form. -/
theorem cutEvaluation_pos_iff_coefficientAt (F : SmallNormalForm.{u}) (hF : 0 < length F) :
    0 < cutEvaluation F ↔ 0 < coefficientAt F 0 := by
  rw [← SignSequence.leadingCoeff_pos_iff, (leading_cutEvaluation F hF).2]

/-- The least exponent of the native Hahn carrier is the dual of the first
formal growth exponent. -/
theorem hahn_orderTop_eq_first (F : SmallNormalForm.{u}) (hF : 0 < length F) :
    (ofLex F.val).orderTop =
      ((OrderDual.toDual (F.exp ⟨0, hF⟩).val : _root_.Surreal.{u}ᵒᵈ) :
        WithTop (_root_.Surreal.{u}ᵒᵈ)) := by
  apply _root_.HahnSeries.orderTop_eq_of_le
  · exact (F.exp ⟨0, hF⟩).property
  · intro a ha
    change OrderDual.ofDual a ≤ (F.exp ⟨0, hF⟩).val
    obtain ⟨i, hi⟩ := _root_.SurrealHahnSeries.eq_exp_of_mem_support (x := F)
      (i := OrderDual.ofDual a) ha
    rw [← hi]
    apply _root_.SurrealHahnSeries.exp_anti
    change (0 : Ordinal.{u}) ≤ i.val
    exact zero_le

/-- The native Hahn leading coefficient is exactly the first formal coefficient. -/
theorem hahn_leadingCoeff_eq_coefficientAt (F : SmallNormalForm.{u}) (hF : 0 < length F) :
    (ofLex F.val).leadingCoeff = coefficientAt F 0 := by
  rw [_root_.HahnSeries.leadingCoeff, hahn_orderTop_eq_first F hF]
  exact _root_.SurrealHahnSeries.coeff_exp F ⟨0, hF⟩

/-- Actual and formal leading coefficients agree, including the empty form. -/
theorem leadingCoeff_cutEvaluation (F : SmallNormalForm.{u}) :
    SignSequence.leadingCoeff (cutEvaluation F) = (ofLex F.val).leadingCoeff := by
  by_cases hF : F = 0
  · subst F
    rw [cutEvaluation_zero, SignSequence.leadingCoeff_zero]
    exact _root_.HahnSeries.leadingCoeff_zero.symm
  have hlen : 0 < length F := bot_lt_iff_ne_bot.mpr ((length_eq_zero F).not.mpr hF)
  rw [(leading_cutEvaluation F hlen).2, hahn_leadingCoeff_eq_coefficientAt F hlen]

/-- The canonical candidate preserves and reflects positivity. This alone
does not compare the candidates of two arbitrary distinct formal forms. -/
theorem cutEvaluation_pos_iff (F : SmallNormalForm.{u}) :
    0 < cutEvaluation F ↔ 0 < F := by
  rw [← SignSequence.leadingCoeff_pos_iff, leadingCoeff_cutEvaluation]
  exact _root_.HahnSeries.leadingCoeff_pos_iff

/-- Positivity together with the zero characterization gives nonnegativity. -/
theorem cutEvaluation_nonneg_iff (F : SmallNormalForm.{u}) :
    0 ≤ cutEvaluation F ↔ 0 ≤ F := by
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt]
  apply or_congr _ (cutEvaluation_pos_iff F)
  constructor
  · intro h
    exact ((cutEvaluation_eq_zero_iff F).mp h.symm).symm
  · intro h
    exact ((cutEvaluation_eq_zero_iff F).mpr h.symm).symm

end

end Surreal.Foundations.SmallNormalForm
