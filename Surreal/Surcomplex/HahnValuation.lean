import Surreal.Surcomplex.AlgebraicallyClosed
import Surreal.Surcomplex.Valuation
import Surreal.Foundations.SignSequenceHahnValuation

/-!
# Valuation and standard part of actual complex Hahn evaluation

The least complex Hahn exponent is the minimum of the two coordinate
orders. The actual coordinate embedding therefore preserves valuation,
finiteness and infinitesimality. On the finite domain, actual complex
standard part is exactly the zero coefficient.
-/

universe u v

namespace Surreal.Surcomplex

open Foundations

noncomputable section

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

private theorem orderTop_realComplexHahnEquiv (z : Complexify (_root_.HahnSeries Γ ℝ)) :
    (Surreal.HahnSeries.realComplexHahnEquiv z).orderTop =
      min z.re.orderTop z.im.orderTop := by
  apply le_antisymm
  · apply le_min
    · apply _root_.HahnSeries.le_orderTop_iff_forall.mpr
      intro a ha
      have h := _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop ha
      simpa only [Surreal.HahnSeries.coeff_realComplexHahnEquiv, Complex.zero_re]
        using congrArg Complex.re h
    · apply _root_.HahnSeries.le_orderTop_iff_forall.mpr
      intro a ha
      have h := _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop ha
      simpa only [Surreal.HahnSeries.coeff_realComplexHahnEquiv, Complex.zero_im]
        using congrArg Complex.im h
  · apply _root_.HahnSeries.le_orderTop_iff_forall.mpr
    intro a ha
    rw [Surreal.HahnSeries.coeff_realComplexHahnEquiv]
    apply Complex.ext
    · exact _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop (ha.trans_le (min_le_left _ _))
    · exact _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop (ha.trans_le (min_le_right _ _))

variable [Small.{u} Γ]

/-- The full actual complex evaluation preserves the least Hahn valuation exponent. -/
theorem valuation_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) :
    valuation (hahnEmbedding e he z) = WithTop.map e z.orderTop := by
  obtain ⟨z, rfl⟩ := Surreal.HahnSeries.realComplexHahnEquiv.surjective z
  rw [hahnEmbedding_realComplexHahnEquiv, valuation_eq_min_coordinates,
    orderTop_realComplexHahnEquiv]
  change min (SignSequence.valuation (SignSequence.hahnEmbedding e he z.re))
    (SignSequence.valuation (SignSequence.hahnEmbedding e he z.im)) = _
  rw [SignSequence.valuation_hahnEmbedding, SignSequence.valuation_hahnEmbedding]
  exact he.monotone.withTop_map.map_min.symm

/-- Finiteness of a complex value is nonnegative order of its complete Hahn series. -/
theorem isFinite_hahnEmbedding_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) : IsFinite (hahnEmbedding e he z) ↔ 0 ≤ z.orderTop := by
  obtain ⟨z, rfl⟩ := Surreal.HahnSeries.realComplexHahnEquiv.surjective z
  rw [hahnEmbedding_realComplexHahnEquiv, orderTop_realComplexHahnEquiv, le_min_iff]
  exact and_congr (SignSequence.isFinite_hahnEmbedding_iff e he z.re)
    (SignSequence.isFinite_hahnEmbedding_iff e he z.im)

/-- Infinitesimality is positive order, including the zero series. -/
theorem isInfinitesimal_hahnEmbedding_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) : IsInfinitesimal (hahnEmbedding e he z) ↔ 0 < z.orderTop := by
  obtain ⟨z, rfl⟩ := Surreal.HahnSeries.realComplexHahnEquiv.surjective z
  rw [hahnEmbedding_realComplexHahnEquiv, orderTop_realComplexHahnEquiv, lt_min_iff]
  exact and_congr (SignSequence.isInfinitesimal_hahnEmbedding_iff e he z.re)
    (SignSequence.isInfinitesimal_hahnEmbedding_iff e he z.im)

/-- The complex residue is the zero coefficient whenever the value is finite. -/
theorem standardPart_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : _root_.HahnSeries Γ ℂ) (hz : 0 ≤ z.orderTop) :
    standardPart (hahnEmbedding e he z) = z.coeff 0 := by
  obtain ⟨z, rfl⟩ := Surreal.HahnSeries.realComplexHahnEquiv.surjective z
  rw [orderTop_realComplexHahnEquiv, le_min_iff] at hz
  rw [hahnEmbedding_realComplexHahnEquiv, Surreal.HahnSeries.coeff_realComplexHahnEquiv]
  apply Complex.ext
  · exact SignSequence.standardPart_hahnEmbedding e he z.re hz.1
  · exact SignSequence.standardPart_hahnEmbedding e he z.im hz.2

end

end Surreal.Surcomplex
