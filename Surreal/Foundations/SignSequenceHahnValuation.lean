import Surreal.Foundations.SignSequenceHahnEmbedding

/-!
# Valuation and leading coefficients of actual Hahn evaluation

The full workspace embedding preserves the least supported valuation
exponent and the leading real coefficient, including infinity at zero.
Consequently finite and infinitesimal actual values are characterized by
the native Hahn order, and the standard part of a finite value is its zero
coefficient. No finite-support restriction is imposed.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

/-- The actual valuation is the embedded least Hahn exponent, including zero. -/
theorem valuation_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    valuation (hahnEmbedding e he x) = WithTop.map e x.orderTop := by
  by_cases hx : x = 0
  · simp [hx]
  let F := SmallNormalForm.hahnEmbedding e he x
  have hF : F ≠ 0 := by
    intro hz
    apply hx
    exact (SmallNormalForm.hahnEmbedding_injective e he)
      (hz.trans (map_zero (SmallNormalForm.hahnEmbedding e he)).symm)
  have hlen : 0 < SmallNormalForm.length F :=
    bot_lt_iff_ne_bot.mpr ((SmallNormalForm.length_eq_zero F).not.mpr hF)
  have ho := SmallNormalForm.hahn_orderTop_eq_first F hlen
  change (ofLex (SmallNormalForm.hahnEmbedding e he x).val).orderTop = _ at ho
  rw [SmallNormalForm.ofLex_hahnEmbedding, Surreal.HahnSeries.orderTop_workspaceEmbedding,
    ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.map_coe,
    WithTop.coe_inj] at ho
  have ha : SmallNormalForm.exponent F ⟨0, hlen⟩ = -e x.order := by
    apply (toSurreal_inj _ _).mp
    rw [SmallNormalForm.exponent, toSurreal_orderIso_symm, toSurreal_neg]
    exact ho.symm
  rw [hahnEmbedding_apply, SmallNormalForm.valuation_cutEvaluation _ hlen, ha,
    neg_neg, ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.map_coe]

/-- The first nonzero real coefficient is unchanged by actual evaluation. -/
theorem leadingCoeff_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    leadingCoeff (hahnEmbedding e he x) = x.leadingCoeff := by
  by_cases hx : x = 0
  · simp [hx]
  rw [hahnEmbedding_apply, SmallNormalForm.leadingCoeff_cutEvaluation,
    SmallNormalForm.ofLex_hahnEmbedding, _root_.HahnSeries.leadingCoeff,
    Surreal.HahnSeries.orderTop_workspaceEmbedding,
    ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.map_coe]
  change (Surreal.HahnSeries.workspaceEmbedding (SmallNormalForm.hahnGrowthMap e)
    (SmallNormalForm.hahnGrowthMap_strictMono e he) x).coeff
      (SmallNormalForm.hahnGrowthMap e x.order) = x.leadingCoeff
  rw [Surreal.HahnSeries.workspaceEmbedding_coeff, _root_.HahnSeries.leadingCoeff_eq]

/-- Finiteness is exactly nonnegative native Hahn order. -/
theorem isFinite_hahnEmbedding_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    IsFinite (hahnEmbedding e he x) ↔ 0 ≤ x.orderTop := by
  rw [isFinite_iff_valuation_nonneg, valuation_hahnEmbedding]
  by_cases hx : x = 0
  · simp [hx]
  rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.map_coe]
  change ((0 : SignSequence.{u}) : WithTop SignSequence.{u}) ≤ ↑(e x.order) ↔
    ((0 : Γ) : WithTop Γ) ≤ ↑x.order
  rw [WithTop.coe_le_coe, WithTop.coe_le_coe, ← e.map_zero]
  exact he.le_iff_le

/-- Infinitesimality is exactly strictly positive native Hahn order. -/
theorem isInfinitesimal_hahnEmbedding_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    IsInfinitesimal (hahnEmbedding e he x) ↔ 0 < x.orderTop := by
  rw [isInfinitesimal_iff_valuation_pos, valuation_hahnEmbedding]
  by_cases hx : x = 0
  · simp [hx]
  rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.map_coe]
  change ((0 : SignSequence.{u}) : WithTop SignSequence.{u}) < ↑(e x.order) ↔
    ((0 : Γ) : WithTop Γ) < ↑x.order
  rw [WithTop.coe_lt_coe, WithTop.coe_lt_coe, ← e.map_zero]
  exact he.lt_iff_lt

/-- On finite values, actual standard part extracts the zero Hahn coefficient. -/
theorem standardPart_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) (hx : 0 ≤ x.orderTop) :
    standardPart (hahnEmbedding e he x) = x.coeff 0 := by
  apply (infinitesimal_sub_ofReal_iff ((isFinite_hahnEmbedding_iff e he x).mpr hx)).mp
  have hr := Surreal.HahnSeries.orderTop_sub_standardPart_pos
    (⟨x, hx⟩ : Surreal.HahnSeries.nonnegativeSubring Γ ℝ)
  have hv := (isInfinitesimal_hahnEmbedding_iff e he
    (x - _root_.HahnSeries.single 0 (x.coeff 0))).mpr hr
  simpa only [map_sub, hahnEmbedding_single_zero] using hv

end

end Surreal.Foundations.SignSequence
