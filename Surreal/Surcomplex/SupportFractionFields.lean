import Surreal.Algebra.AugmentationFractionField
import Surreal.Surcomplex.IdealMultipliers

/-!
# Actual support rings in the omnific fraction fields

The actual real and complex assertions of `odg:def:lem:ainfrac`.
The denominator omega works for every support-ring element, and both
numerator and denominator have zero constant term.
-/

universe u
namespace Surreal

open Foundations

noncomputable section

namespace Foundations.SignSequence

/-- Positive-growth real monomials belong to the actual purely infinite ideal. -/
theorem isPurelyInfinite_omegaPower (a : SignSequence.{u}) (ha : 0 < a) :
    IsPurelyInfinite (omegaPower a) := by
  rw [IsPurelyInfinite, rawNormalForm_omegaPower]
  apply HahnSeries.purelyInfiniteSeries_single
  change 0 < toSurreal a
  simpa only [toSurreal_zero] using (toSurreal_lt_iff 0 a).mpr ha

/-- The native fraction field of actual omnific integers, embedded in the actual surreal field. -/
abbrev omnificFractionEmbedding : FractionRing OmnificInteger.{u} →+* SignSequence.{u} :=
  AugmentationFractionField.fractionEmbedding nonnegativeSupportSubring constantCoeff (Int.castRingHom ℝ)

/-- Every actual real support-ring element belongs to the embedded native omnific fraction field. -/
theorem nonnegativeSupport_mem_fractionField (x : nonnegativeSupportSubring.{u}) :
    x.val ∈ omnificFractionEmbedding.fieldRange := by
  have hp := isPurelyInfinite_omegaPower (1 : SignSequence.{u}) zero_lt_one
  let d : nonnegativeSupportSubring.{u} := ⟨omegaPower 1, hp.mem_supportRing⟩
  have hd : constantCoeff d = 0 := (isPurelyInfinite_iff d).mp hp
  have hd0 : d ≠ 0 := fun h => omegaPower_ne_zero 1 (congrArg Subtype.val h)
  exact AugmentationFractionField.mem_fractionField _ _ _ d hd hd0 x

/-- The multiplier identity inside the native fraction field of actual omnific integers. -/
theorem omnific_fraction_multiplier_iff (x : FractionRing OmnificInteger.{u}) :
    IsPurelyInfiniteMultiplier (omnificFractionEmbedding x) ↔
      omnificFractionEmbedding x ∈ nonnegativeSupportSubring := purelyInfiniteMultiplier_iff _

end Foundations.SignSequence
namespace Surcomplex

/-- The same positive monomial is purely infinite in the actual complex carrier. -/
theorem isPurelyInfinite_real_omegaPower (a : SignSequence.{u}) (ha : 0 < a) :
    IsPurelyInfinite (ofReal (SignSequence.omegaPower a)) := by
  rw [IsPurelyInfinite, rawNormalForm_real_omegaPower]
  apply HahnSeries.purelyInfiniteSeries_single
  change 0 < SignSequence.toSurreal a
  simpa only [SignSequence.toSurreal_zero] using (SignSequence.toSurreal_lt_iff 0 a).mpr ha

/-- The native Gaussian omnific fraction field embeds into the actual surcomplex field. -/
abbrev gaussianOmnificFractionEmbedding : FractionRing GaussianOmnificInteger.{u} →+* Surcomplex.{u} :=
  AugmentationFractionField.fractionEmbedding nonnegativeSupportSubring constantCoeff GaussianInt.toComplex

/-- Every actual complex support-ring element belongs to the Gaussian omnific fraction field. -/
theorem nonnegativeSupport_mem_fractionField (z : nonnegativeSupportSubring.{u}) :
    z.val ∈ gaussianOmnificFractionEmbedding.fieldRange := by
  have hp := isPurelyInfinite_real_omegaPower (1 : SignSequence.{u}) zero_lt_one
  let d : nonnegativeSupportSubring.{u} := ⟨ofReal (SignSequence.omegaPower 1), hp.mem_supportRing⟩
  have hd : constantCoeff d = 0 := (isPurelyInfinite_iff d).mp hp
  have hd0 : d ≠ 0 := by
    intro h
    have he : ofReal (SignSequence.omegaPower (1 : SignSequence.{u})) = ofReal 0 :=
      (congrArg Subtype.val h).trans (map_zero ofReal).symm
    exact SignSequence.omegaPower_ne_zero 1 (ofReal_injective he)
  exact AugmentationFractionField.mem_fractionField _ _ _ d hd hd0 z

/-- The multiplier identity inside the native Gaussian omnific fraction field. -/
theorem gaussianOmnific_fraction_multiplier_iff (z : FractionRing GaussianOmnificInteger.{u}) :
    IsPurelyInfiniteMultiplier (gaussianOmnificFractionEmbedding z) ↔
      gaussianOmnificFractionEmbedding z ∈ nonnegativeSupportSubring := purelyInfiniteMultiplier_iff _

end Surcomplex
end
end Surreal
