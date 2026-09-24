import Surreal.Foundations.OmnificExponentAutomorphisms
import Surreal.Foundations.SignSequenceStrongAlgebra

/-!
# Strong sums and valuation under actual exponent automorphisms

Completes `prop:hahn-lift` and `eq:hahn-lift` in the exponential automorphism
rigidity report, including the actual canonical-lift clause of `thm:dilation`.
-/

universe u v
namespace Surreal.Foundations.SignSequence
open SmallNormalForm
noncomputable section

/-- The constructed map agrees with native Hahn exponent transport on every canonical form. -/
theorem rawNormalForm_exponentAutomorphism
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (x : SignSequence.{u}) :
    rawNormalForm (exponentAutomorphism e x) =
      Surreal.HahnSeries.workspaceEmbedding (exponentHahnMap e) (exponentHahnMap_strictMono e)
        (rawNormalForm x) := by
  change ofLex (normalForm (exponentAutomorphism e x)).val = _
  rw [normalForm_exponentAutomorphism]
  rfl

/-- The canonical lift preserves strong summability, without a bound on the index universe. -/
theorem StronglySummable.exponentAutomorphism {ι : Type v} {f : ι → SignSequence.{u}}
    (hf : StronglySummable f) (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    StronglySummable (fun i => SignSequence.exponentAutomorphism e (f i)) := by
  apply stronglySummable_of_hahnFamily
    (Surreal.HahnSeries.mapExponentsFamily (exponentHahnMap e)
      (exponentHahnMap_strictMono e) hf.toHahnFamily)
  intro i
  exact (rawNormalForm_exponentAutomorphism e (f i)).symm

/-- Applying the inverse proves reflection of both strong summability conditions. -/
theorem stronglySummable_exponentAutomorphism_iff {ι : Type v} (f : ι → SignSequence.{u})
    (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    StronglySummable (fun i => exponentAutomorphism e (f i)) ↔ StronglySummable f := by
  constructor
  · intro hf
    simpa only [exponentAutomorphism_inverse] using hf.exponentAutomorphism e.symm
  · exact fun hf => hf.exponentAutomorphism e

/-- The canonical lift commutes with every existing actual strong sum. -/
theorem exponentAutomorphism_strongSum {ι : Type v} [Small.{u} ι]
    {f : ι → SignSequence.{u}} (hf : StronglySummable f)
    (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    exponentAutomorphism e (strongSum f hf) =
      strongSum (fun i => exponentAutomorphism e (f i)) (hf.exponentAutomorphism e) := by
  apply rawNormalForm_injective
  rw [rawNormalForm_exponentAutomorphism, rawNormalForm_strongSum, rawNormalForm_strongSum]
  have hs : (hf.exponentAutomorphism e).toHahnFamily =
      Surreal.HahnSeries.mapExponentsFamily (exponentHahnMap e)
        (exponentHahnMap_strictMono e) hf.toHahnFamily := by
    ext1 i
    exact rawNormalForm_exponentAutomorphism e (f i)
  rw [hs, Surreal.HahnSeries.hsum_mapExponentsFamily]

/-- The largest growth exponent is transported by the exponent automorphism. -/
theorem leadingExponent_exponentAutomorphism
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (x : SignSequence.{u}) :
    leadingExponent (exponentAutomorphism e x) = e (leadingExponent x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hy : exponentAutomorphism e x ≠ 0 :=
    (map_ne_zero_iff (exponentAutomorphism e) (exponentAutomorphism e).injective).mpr hx
  apply le_antisymm
  · have hs := leadingExponent_mem_normalForm hy
    rw [support_exponentAutomorphism] at hs
    obtain ⟨a, ha, he⟩ := hs
    rw [← he]
    exact e.strictMono.monotone (normalForm_support_le_leadingExponent x ha)
  · apply normalForm_support_le_leadingExponent
    rw [support_exponentAutomorphism]
    exact Set.mem_image_of_mem e (leadingExponent_mem_normalForm hx)

/-- The natural additive valuation intertwines with the same exponent map, including infinity. -/
theorem valuation_exponentAutomorphism
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (x : SignSequence.{u}) :
    valuation (exponentAutomorphism e x) = WithTop.map e (valuation x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hy : exponentAutomorphism e x ≠ 0 :=
    (map_ne_zero_iff (exponentAutomorphism e) (exponentAutomorphism e).injective).mpr hx
  rw [valuation_of_ne_zero hy, valuation_of_ne_zero hx, WithTop.map_coe,
    leadingExponent_exponentAutomorphism, map_neg]

/-- The canonical lift preserves the actual field order. -/
theorem exponentAutomorphism_strictMono (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    StrictMono (exponentAutomorphism e) := by
  rw [← omnificAutomorphismExtension_exponentAutomorphism]
  exact omnificAutomorphismExtension_strictMono _

/-- The canonical exponent lift as an actual ordered field automorphism. -/
def exponentOrderAutomorphism (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    SignSequence.{u} ≃+*o SignSequence.{u} where
  __ := exponentAutomorphism e
  map_le_map_iff' := (exponentAutomorphism_strictMono e).le_iff_le

end
end Surreal.Foundations.SignSequence
