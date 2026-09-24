import Surreal.Algebra.NormalizationConductor
import Surreal.Foundations.OmnificNormalizationDensity

/-!
# The actual omnific normalization

The full actual-field clause of `osq:nm:thm:normalization`: proper dense
inclusions, zero conductor and failure of generation by any
lower-universe-small set. The fixed countable-support model is separate.
-/

universe u
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Any nonzero omnific integer has an integral-unit multiple outside the omnific ring. -/
theorem omnific_normalization_unit_obstruction (a : OmnificInteger.{u}) (ha : a ≠ 0) :
    ∃ u : integralClosure OmnificInteger SignSequence.{u}, IsUnit u ∧
      0 < |omnificToSurreal a * (u : SignSequence)| ∧
      |omnificToSurreal a * (u : SignSequence)| < 1 ∧
      ¬ ∃ b : OmnificInteger, omnificToSurreal b = omnificToSurreal a * (u : SignSequence) :=
  NormalizationConductor.exists_unit_multiple_not_mem existsUnique_omnific_integerPart a ha

/-- The conductor from the actual omnific ring into its integral closure is the zero ideal. -/
theorem omnific_normalization_conductor_eq_bot :
    NormalizationConductor.conductor OmnificInteger SignSequence.{u} = ⊥ :=
  NormalizationConductor.conductor_eq_bot existsUnique_omnific_integerPart

/-- No lower-universe-small set generates the actual normalization as an omnific algebra. -/
theorem omnific_normalization_not_small_generated (s : Set SignSequence.{u}) [Small.{u} s] :
    Algebra.adjoin OmnificInteger s ≠ integralClosure OmnificInteger SignSequence := by
  intro he
  obtain ⟨d, hd, _, hs⟩ := omnific_adjoin_conductor_nonzero s
  have hmem : d ∈ NormalizationConductor.conductor OmnificInteger SignSequence.{u} := by
    intro x
    obtain ⟨z, _, hz⟩ := hs (x : SignSequence) (he.symm ▸ x.property)
    exact ⟨z, hz⟩
  rw [omnific_normalization_conductor_eq_bot, Ideal.mem_bot] at hmem
  exact hd hmem

/-- The normalization theorem on the actual universe-indexed surreal field. -/
theorem omnific_normalization :
    (⊥ : Subalgebra OmnificInteger SignSequence.{u}) < integralClosure OmnificInteger SignSequence ∧
      integralClosure OmnificInteger SignSequence.{u} < ⊤ ∧
      Dense (integralClosure OmnificInteger SignSequence.{u} : Set SignSequence) ∧
      NormalizationConductor.conductor OmnificInteger SignSequence.{u} = ⊥ ∧
      ∀ (s : Set SignSequence.{u}) [Small.{u} s],
        Algebra.adjoin OmnificInteger s ≠ integralClosure OmnificInteger SignSequence :=
  ⟨omnific_bot_lt_integralClosure, omnific_integralClosure_lt_top,
    omnific_integralClosure_dense, omnific_normalization_conductor_eq_bot,
    omnific_normalization_not_small_generated⟩

end
end Surreal.Foundations.SignSequence
