import Surreal.Surcomplex.StrongAlgebra

/-!
# Realizing small complex Hahn forms in the actual surcomplex field

The support-size prerequisite for the coefficientwise lift in
`odg:def:prop:coeffaut`. Only Hahn forms with lower-universe-small support
are realized; no surjectivity onto a full unrestricted Hahn field is asserted.
-/

universe u
namespace Surreal.Surcomplex
open Foundations
noncomputable section

private theorem small_real_support (F : _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (hF : Small.{u} F.support) : Small.{u} (HahnSeries.realComplexHahnEquiv.symm F).re.support := by
  letI := hF
  apply small_subset (s := F.support)
  intro a ha hz
  apply ha
  change (F.coeff a).re = 0
  rw [hz]
  rfl

private theorem small_imaginary_support (F : _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (hF : Small.{u} F.support) : Small.{u} (HahnSeries.realComplexHahnEquiv.symm F).im.support := by
  letI := hF
  apply small_subset (s := F.support)
  intro a ha hz
  apply ha
  change (F.coeff a).im = 0
  rw [hz]
  rfl

/-- Evaluate the real and imaginary small forms using the proved actual normal-form equivalence. -/
def ofSmallHahn (F : _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (hF : Small.{u} F.support) : Surcomplex.{u} :=
  ⟨SmallNormalForm.cutEvaluation (SmallNormalForm.ofHahn
      (HahnSeries.realComplexHahnEquiv.symm F).re (small_real_support F hF)),
    SmallNormalForm.cutEvaluation (SmallNormalForm.ofHahn
      (HahnSeries.realComplexHahnEquiv.symm F).im (small_imaginary_support F hF))⟩

/-- Realization has exactly the given complex coefficients. -/
@[simp] theorem rawNormalForm_ofSmallHahn (F : _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℂ)
    (hF : Small.{u} F.support) : rawNormalForm (ofSmallHahn F hF) = F := by
  change HahnSeries.realComplexHahnEquiv
    ⟨ofLex (SmallNormalForm.normalForm (SmallNormalForm.cutEvaluation _)).val,
      ofLex (SmallNormalForm.normalForm (SmallNormalForm.cutEvaluation _)).val⟩ = F
  rw [SmallNormalForm.normalForm_cutEvaluation, SmallNormalForm.normalForm_cutEvaluation,
    SmallNormalForm.ofLex_ofHahn, SmallNormalForm.ofLex_ofHahn]
  exact HahnSeries.realComplexHahnEquiv.apply_symm_apply F

@[simp] theorem ofSmallHahn_rawNormalForm (z : Surcomplex.{u}) :
    ofSmallHahn (rawNormalForm z) (small_support_rawNormalForm z) = z := by
  apply rawNormalForm_injective
  exact rawNormalForm_ofSmallHahn _ _

/-- The image of actual normal-form extraction consists exactly of the small-support forms. -/
theorem exists_rawNormalForm_iff_small (F : _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℂ) :
    (∃ z : Surcomplex.{u}, rawNormalForm z = F) ↔ Small.{u} F.support := by
  constructor
  · rintro ⟨z, rfl⟩
    exact small_support_rawNormalForm z
  · intro hF
    exact ⟨ofSmallHahn F hF, rawNormalForm_ofSmallHahn F hF⟩

end
end Surreal.Surcomplex
