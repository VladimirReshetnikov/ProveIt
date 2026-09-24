import Surreal.Foundations.SmallNormalFormHahnEmbedding
import Surreal.Foundations.SmallNormalFormFieldEquiv

/-!
# Actual surreal embeddings of small real Hahn workspaces

An increasing additive map from a small exponent group into the sign field
embeds the complete real Hahn workspace into actual surreal numbers. The
formal exponent embedding is composed with the proved normal-form field
equivalence. Both arithmetic and the native lexicographic Hahn order are
preserved; single terms use the convention t^a = omega^(-a).
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

/-- Evaluate every series in a small real Hahn workspace as an actual surreal number. -/
def hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    _root_.HahnSeries Γ ℝ →+* SignSequence.{u} :=
  SmallNormalForm.cutEvaluationRingHom.comp (SmallNormalForm.hahnEmbedding e he)

@[simp] theorem hahnEmbedding_apply (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    hahnEmbedding e he x = SmallNormalForm.cutEvaluation (SmallNormalForm.hahnEmbedding e he x) :=
  rfl

/-- Inverse normal-form extraction recovers exactly the embedded formal series. -/
@[simp] theorem normalForm_hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : _root_.HahnSeries Γ ℝ) :
    SmallNormalForm.normalForm (hahnEmbedding e he x) = SmallNormalForm.hahnEmbedding e he x :=
  SmallNormalForm.normalForm_cutEvaluation _

/-- A workspace monomial is its actual real coefficient times the corresponding t-monomial. -/
@[simp] theorem hahnEmbedding_single (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (a : Γ) (r : ℝ) :
    hahnEmbedding e he (_root_.HahnSeries.single a r) = ofReal r * tMonomial (e a) := by
  rw [hahnEmbedding_apply, SmallNormalForm.hahnEmbedding_single,
    SmallNormalForm.cutEvaluation_single]
  rfl

/-- Constant real series retain their actual real values. -/
@[simp] theorem hahnEmbedding_single_zero (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (r : ℝ) : hahnEmbedding e he (_root_.HahnSeries.single 0 r) = ofReal r := by
  rw [hahnEmbedding_single, map_zero, tMonomial_zero, mul_one]

/-- Distinct Hahn series remain distinct after actual evaluation. -/
theorem hahnEmbedding_injective (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    Function.Injective (hahnEmbedding e he) :=
  SmallNormalForm.cutEvaluation_injective.comp (SmallNormalForm.hahnEmbedding_injective e he)

/-- Actual comparison agrees with the native Hahn lexicographic comparison. -/
@[simp] theorem hahnEmbedding_le_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x y : _root_.HahnSeries Γ ℝ) :
    hahnEmbedding e he x ≤ hahnEmbedding e he y ↔ toLex x ≤ toLex y := by
  rw [hahnEmbedding_apply, hahnEmbedding_apply, SmallNormalForm.cutEvaluation_le_iff]
  let f : Γ ↪o _root_.Surreal.{u}ᵒᵈ :=
    ⟨⟨SmallNormalForm.hahnGrowthMap e, (SmallNormalForm.hahnGrowthMap_strictMono e he).injective⟩,
      (SmallNormalForm.hahnGrowthMap_strictMono e he).le_iff_le⟩
  change toLex (ofLex (SmallNormalForm.hahnEmbedding e he x).val) ≤
    toLex (ofLex (SmallNormalForm.hahnEmbedding e he y).val) ↔ _
  rw [SmallNormalForm.ofLex_hahnEmbedding, SmallNormalForm.ofLex_hahnEmbedding]
  exact (_root_.HahnSeries.embDomainOrderEmbedding f (R := ℝ)).le_iff_le

/-- Strict Hahn comparison is preserved and reflected as well. -/
@[simp] theorem hahnEmbedding_lt_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x y : _root_.HahnSeries Γ ℝ) :
    hahnEmbedding e he x < hahnEmbedding e he y ↔ toLex x < toLex y := by
  simpa only [not_le] using (hahnEmbedding_le_iff e he y x).not

/-- The actual embedding with its native ordered Hahn domain. -/
def hahnOrderEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    Lex (_root_.HahnSeries Γ ℝ) ↪o SignSequence.{u} where
  toFun x := hahnEmbedding e he (ofLex x)
  inj' := (hahnEmbedding_injective e he).comp ofLex.injective
  map_rel_iff' := hahnEmbedding_le_iff e he _ _

@[simp] theorem hahnOrderEmbedding_apply (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : Lex (_root_.HahnSeries Γ ℝ)) :
    hahnOrderEmbedding e he x = hahnEmbedding e he (ofLex x) := rfl

/-- The same map packages the proved arithmetic and order preservation together. -/
def hahnOrderRingHom (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    Lex (_root_.HahnSeries Γ ℝ) →+*o SignSequence.{u} where
  toFun x := hahnEmbedding e he (ofLex x)
  map_zero' := (hahnEmbedding e he).map_zero
  map_one' := (hahnEmbedding e he).map_one
  map_add' x y := (hahnEmbedding e he).map_add (ofLex x) (ofLex y)
  map_mul' x y := (hahnEmbedding e he).map_mul (ofLex x) (ofLex y)
  monotone' := (hahnOrderEmbedding e he).monotone

@[simp] theorem hahnOrderRingHom_apply (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : Lex (_root_.HahnSeries Γ ℝ)) :
    hahnOrderRingHom e he x = hahnEmbedding e he (ofLex x) := rfl

end

end Surreal.Foundations.SignSequence
