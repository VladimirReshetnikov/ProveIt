import Surreal.Surcomplex.HahnLeading
import Surreal.Foundations.SmallNormalFormWorkspace

/-!
# Common complex Hahn workspaces for actual small families

The real and imaginary normal forms of a small surcomplex family fit into
one small divisible exponent group. The complete complex Hahn field on that
group embeds into the actual surcomplex field, and explicit coordinate
pullbacks recover every member. Its image is a small subfield, independently
of any finite-support or strong-summability restriction on the input family.
-/

universe u v

namespace Surreal.Surcomplex

open Foundations

noncomputable section

variable {ι : Type v}

/-- Both coordinates of every member, represented by their canonical formal normal forms. -/
def familyCoordinateForms (F : ι → Surcomplex.{u}) : ι ⊕ ι → SmallNormalForm.{u} :=
  Sum.elim (fun i => SmallNormalForm.normalForm (F i).re)
    (fun i => SmallNormalForm.normalForm (F i).im)

/-- One rational-span exponent workspace contains every coordinate support. -/
abbrev familyWorkspaceExponents (F : ι → Surcomplex.{u}) :=
  SignSequence.workspaceExponents (⋃ i, SmallNormalForm.support (familyCoordinateForms F i))

variable [Small.{u} ι]

/-- Embed the entire common complex Hahn workspace into actual surcomplex numbers. -/
def familyWorkspaceEmbedding (F : ι → Surcomplex.{u}) :
    _root_.HahnSeries (familyWorkspaceExponents F) ℂ →+* Surcomplex.{u} :=
  hahnEmbedding (familyWorkspaceExponents F).subtype.toAddMonoidHom (fun _ _ h => h)

theorem familyWorkspaceEmbedding_injective (F : ι → Surcomplex.{u}) :
    Function.Injective (familyWorkspaceEmbedding F) := hahnEmbedding_injective _ _

/-- The common workspace retains ordinary complex constants exactly. -/
@[simp] theorem familyWorkspaceEmbedding_single_zero (F : ι → Surcomplex.{u}) (c : ℂ) :
    familyWorkspaceEmbedding F (_root_.HahnSeries.single 0 c) = ofComplex c :=
  hahnEmbedding_single_zero _ _ c

/-- Pull back both complete coordinate normal forms and combine them as a complex Hahn series. -/
def familyHahnPreimage (F : ι → Surcomplex.{u}) (i : ι) :
    _root_.HahnSeries (familyWorkspaceExponents F) ℂ :=
  HahnSeries.realComplexHahnEquiv
    ⟨SmallNormalForm.familyHahnPreimage (familyCoordinateForms F) (Sum.inl i),
      SmallNormalForm.familyHahnPreimage (familyCoordinateForms F) (Sum.inr i)⟩

omit [Small.{u} ι] in
/-- The explicit preimage uses the original two coefficients at the negative growth exponent. -/
@[simp] theorem coeff_familyHahnPreimage (F : ι → Surcomplex.{u}) (i : ι)
    (a : familyWorkspaceExponents F) :
    (familyHahnPreimage F i).coeff a =
      ⟨SmallNormalForm.coeff (SmallNormalForm.normalForm (F i).re) (-a.val),
        SmallNormalForm.coeff (SmallNormalForm.normalForm (F i).im) (-a.val)⟩ :=
  HahnSeries.coeff_realComplexHahnEquiv _ _

/-- Every member of the original family is represented exactly in the common workspace. -/
@[simp] theorem familyWorkspaceEmbedding_preimage (F : ι → Surcomplex.{u}) (i : ι) :
    familyWorkspaceEmbedding F (familyHahnPreimage F i) = F i := by
  rw [familyWorkspaceEmbedding, familyHahnPreimage, hahnEmbedding_realComplexHahnEquiv]
  apply ext
  · change SmallNormalForm.cutEvaluation
      (SmallNormalForm.familyWorkspaceEmbedding (familyCoordinateForms F)
        (SmallNormalForm.familyHahnPreimage (familyCoordinateForms F) (Sum.inl i))) = _
    rw [SmallNormalForm.familyWorkspaceEmbedding_preimage]
    exact SmallNormalForm.cutEvaluation_normalForm _
  · change SmallNormalForm.cutEvaluation
      (SmallNormalForm.familyWorkspaceEmbedding (familyCoordinateForms F)
        (SmallNormalForm.familyHahnPreimage (familyCoordinateForms F) (Sum.inr i))) = _
    rw [SmallNormalForm.familyWorkspaceEmbedding_preimage]
    exact SmallNormalForm.cutEvaluation_normalForm _

theorem mem_range_familyWorkspaceEmbedding (F : ι → Surcomplex.{u}) (i : ι) :
    F i ∈ Set.range (familyWorkspaceEmbedding F) :=
  ⟨familyHahnPreimage F i, familyWorkspaceEmbedding_preimage F i⟩

/-- The actual common workspace is a subfield, closed under all field operations. -/
def familyWorkspaceSubfield (F : ι → Surcomplex.{u}) : Subfield Surcomplex.{u} :=
  (familyWorkspaceEmbedding F).fieldRange

theorem mem_familyWorkspaceSubfield (F : ι → Surcomplex.{u}) (i : ι) :
    F i ∈ familyWorkspaceSubfield F := mem_range_familyWorkspaceEmbedding F i

/-- The entire actual workspace, not only the input family, is small in the birthday universe. -/
instance small_familyWorkspaceSubfield (F : ι → Surcomplex.{u}) :
    Small.{u} (familyWorkspaceSubfield F) := by
  haveI : Small.{u} (_root_.HahnSeries (familyWorkspaceExponents F) ℂ) :=
    small_of_injective (f := fun x => x.coeff) (fun _ _ h => _root_.HahnSeries.ext h)
  change Small.{u} (Set.range (familyWorkspaceEmbedding F))
  infer_instance

/-- The actual workspace is isomorphic to the full complex Hahn field used to construct it. -/
def familyWorkspaceEquiv (F : ι → Surcomplex.{u}) :
    _root_.HahnSeries (familyWorkspaceExponents F) ℂ ≃+* familyWorkspaceSubfield F :=
  (familyWorkspaceEmbedding F).rangeRestrictFieldEquiv

end

end Surreal.Surcomplex
