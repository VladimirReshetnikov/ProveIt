import Surreal.Foundations.SignSequenceHahnEmbedding
import Surreal.Foundations.SmallNormalFormWorkspace

/-!
# Common Hahn workspaces for actual surreal families

Normal-form extraction places any small family of actual sign numbers in
one small divisible exponent workspace. Composing its formal Hahn embedding
with canonical evaluation gives an injective actual embedding and explicit
preimages of every family member. Its range is a small subfield, so it is
closed under the ordinary field operations. Polynomial coefficients descend
to the same construction with degree preserved.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

section Family

variable {ι : Type v} [Small.{u} ι]

/-- One actual Hahn embedding contains the normal-form supports of the whole family. -/
def familyWorkspaceEmbedding (F : ι → SignSequence.{u}) :
    _root_.HahnSeries
      (workspaceExponents (⋃ i, SmallNormalForm.support (SmallNormalForm.normalForm (F i))))
      ℝ →+* SignSequence.{u} :=
  SmallNormalForm.cutEvaluationRingHom.comp
    (SmallNormalForm.familyWorkspaceEmbedding (fun i => SmallNormalForm.normalForm (F i)))

@[simp] theorem familyWorkspaceEmbedding_apply (F : ι → SignSequence.{u})
    (x : _root_.HahnSeries
      (workspaceExponents (⋃ i, SmallNormalForm.support (SmallNormalForm.normalForm (F i)))) ℝ) :
    familyWorkspaceEmbedding F x = SmallNormalForm.cutEvaluation
      (SmallNormalForm.familyWorkspaceEmbedding (fun i => SmallNormalForm.normalForm (F i)) x) :=
  rfl

theorem familyWorkspaceEmbedding_injective (F : ι → SignSequence.{u}) :
    Function.Injective (familyWorkspaceEmbedding F) :=
  SmallNormalForm.cutEvaluation_injective.comp
    (SmallNormalForm.familyWorkspaceEmbedding_injective (fun i => SmallNormalForm.normalForm (F i)))

/-- The common embedding preserves the native Hahn lexicographic order. -/
@[simp] theorem familyWorkspaceEmbedding_le_iff (F : ι → SignSequence.{u})
    (x y : _root_.HahnSeries
      (workspaceExponents (⋃ i, SmallNormalForm.support (SmallNormalForm.normalForm (F i)))) ℝ) :
    familyWorkspaceEmbedding F x ≤ familyWorkspaceEmbedding F y ↔ toLex x ≤ toLex y :=
  hahnEmbedding_le_iff _ _ x y

/-- The constant real series have their actual real values in the common workspace. -/
@[simp] theorem familyWorkspaceEmbedding_single_zero (F : ι → SignSequence.{u}) (r : ℝ) :
    familyWorkspaceEmbedding F (_root_.HahnSeries.single 0 r) = ofReal r :=
  hahnEmbedding_single_zero _ _ r

/-- Pull back a family member's full normal form to its common Hahn workspace. -/
def familyHahnPreimage (F : ι → SignSequence.{u}) (i : ι) :
    _root_.HahnSeries
      (workspaceExponents (⋃ j, SmallNormalForm.support (SmallNormalForm.normalForm (F j)))) ℝ :=
  SmallNormalForm.familyHahnPreimage (fun j => SmallNormalForm.normalForm (F j)) i

/-- The common workspace represents every input exactly. -/
@[simp] theorem familyWorkspaceEmbedding_preimage (F : ι → SignSequence.{u}) (i : ι) :
    familyWorkspaceEmbedding F (familyHahnPreimage F i) = F i := by
  rw [familyWorkspaceEmbedding_apply]
  change SmallNormalForm.cutEvaluation
    (SmallNormalForm.familyWorkspaceEmbedding (fun j => SmallNormalForm.normalForm (F j))
      (SmallNormalForm.familyHahnPreimage (fun j => SmallNormalForm.normalForm (F j)) i)) = _
  rw [SmallNormalForm.familyWorkspaceEmbedding_preimage, SmallNormalForm.cutEvaluation_normalForm]

theorem mem_range_familyWorkspaceEmbedding (F : ι → SignSequence.{u}) (i : ι) :
    F i ∈ Set.range (familyWorkspaceEmbedding F) :=
  ⟨familyHahnPreimage F i, familyWorkspaceEmbedding_preimage F i⟩

/-- The actual image is a subfield, retaining native closure under field operations. -/
def familyWorkspaceSubfield (F : ι → SignSequence.{u}) : Subfield SignSequence.{u} :=
  (familyWorkspaceEmbedding F).fieldRange

theorem mem_familyWorkspaceSubfield (F : ι → SignSequence.{u}) (i : ι) :
    F i ∈ familyWorkspaceSubfield F := mem_range_familyWorkspaceEmbedding F i

/-- The common actual subfield remains small in the birthday universe. -/
instance small_familyWorkspaceSubfield (F : ι → SignSequence.{u}) :
    Small.{u} (familyWorkspaceSubfield F) := by
  haveI : Small.{u} (_root_.HahnSeries
      (workspaceExponents (⋃ i, SmallNormalForm.support (SmallNormalForm.normalForm (F i)))) ℝ) :=
    small_of_injective (f := fun x => x.coeff) (fun _ _ h => _root_.HahnSeries.ext h)
  change Small.{u} (Set.range (familyWorkspaceEmbedding F))
  infer_instance

end Family

/-- Every actual polynomial descends to a small divisible real Hahn coefficient workspace. -/
theorem exists_polynomial_hahn_preimage (P : Polynomial SignSequence.{u}) :
    ∃ Q : Polynomial (_root_.HahnSeries
      (workspaceExponents
        (⋃ n, SmallNormalForm.support (SmallNormalForm.normalForm (P.coeff n)))) ℝ),
      Q.map (familyWorkspaceEmbedding P.coeff) = P := by
  apply (Polynomial.mem_lifts P).mp
  apply (Polynomial.lifts_iff_coeff_lifts P).mpr
  exact mem_range_familyWorkspaceEmbedding P.coeff

/-- The injective coefficient embedding preserves the localized polynomial's degree. -/
theorem exists_polynomial_hahn_preimage_natDegree (P : Polynomial SignSequence.{u}) :
    ∃ Q : Polynomial (_root_.HahnSeries
      (workspaceExponents
        (⋃ n, SmallNormalForm.support (SmallNormalForm.normalForm (P.coeff n)))) ℝ),
      Q.map (familyWorkspaceEmbedding P.coeff) = P ∧ Q.natDegree = P.natDegree := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_hahn_preimage P
  refine ⟨Q, hQ, ?_⟩
  have hd := Polynomial.natDegree_map_eq_of_injective (familyWorkspaceEmbedding_injective P.coeff) Q
  rw [hQ] at hd
  exact hd.symm

end

end Surreal.Foundations.SignSequence
