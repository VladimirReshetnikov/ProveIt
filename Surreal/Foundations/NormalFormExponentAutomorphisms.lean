import Surreal.Foundations.SmallNormalFormFieldEquiv
import Surreal.Foundations.SmallNormalFormHahnEmbedding

/-!
# Exponent automorphisms of actual small normal forms

Transport through an ordered additive automorphism of the actual exponent
field, retaining lower-universe-small support. This supplies the general
construction behind `odg:def:ex:dilation`.
-/

universe u
namespace Surreal.Foundations.SmallNormalForm

open SignSequence
noncomputable section

/-- The same exponent map on the native, decreasing-growth Hahn indices. -/
def exponentHahnMap (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    _root_.Surreal.{u}ᵒᵈ →+ _root_.Surreal.{u}ᵒᵈ where
  toFun a := OrderDual.toDual (toSurreal (e (toSurrealRingEquiv.symm (OrderDual.ofDual a))))
  map_zero' := by simp
  map_add' a b := by simp

theorem exponentHahnMap_strictMono (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    StrictMono (exponentHahnMap e) := by
  intro a b h
  change toSurreal (e (toSurrealRingEquiv.symm (OrderDual.ofDual b))) <
    toSurreal (e (toSurrealRingEquiv.symm (OrderDual.ofDual a)))
  apply (toSurreal_lt_iff _ _).mpr
  apply e.strictMono
  exact toSurrealOrderIso.symm.strictMono h

@[simp] theorem exponentHahnMap_toSurreal (e : SignSequence.{u} ≃+o SignSequence.{u})
    (a : SignSequence.{u}) :
    exponentHahnMap e (OrderDual.toDual (toSurreal a)) = OrderDual.toDual (toSurreal (e a)) := by
  change OrderDual.toDual (toSurreal (e (toSurrealRingEquiv.symm (toSurrealRingEquiv a)))) = _
  rw [RingEquiv.symm_apply_apply]

private theorem small_exponent_image (e : SignSequence.{u} ≃+o SignSequence.{u})
    (F : SmallNormalForm.{u}) :
    Small.{u} (Surreal.HahnSeries.workspaceEmbedding (exponentHahnMap e)
      (exponentHahnMap_strictMono e) (ofLex F.val)).support := by
  letI : Small.{u} (ofLex F.val).support := _root_.SurrealHahnSeries.small_support F
  rw [Surreal.HahnSeries.support_workspaceEmbedding]
  exact small_image _ _

/-- Exponent substitution on the small formal field. -/
def mapExponents (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    SmallNormalForm.{u} →+* SmallNormalForm.{u} where
  toFun F := ofHahn (Surreal.HahnSeries.workspaceEmbedding (exponentHahnMap e)
    (exponentHahnMap_strictMono e) (ofLex F.val)) (small_exponent_image e F)
  map_zero' := by
    apply Subtype.ext
    change toLex (Surreal.HahnSeries.workspaceEmbedding (exponentHahnMap e) (exponentHahnMap_strictMono e) 0) = _
    rw [map_zero]; rfl
  map_one' := by
    apply Subtype.ext
    change toLex (Surreal.HahnSeries.workspaceEmbedding (exponentHahnMap e) (exponentHahnMap_strictMono e) 1) = _
    rw [map_one]; rfl
  map_add' F G := by
    apply Subtype.ext
    change toLex (Surreal.HahnSeries.workspaceEmbedding (exponentHahnMap e) (exponentHahnMap_strictMono e) (ofLex F.val + ofLex G.val)) = _
    rw [map_add]; rfl
  map_mul' F G := by
    apply Subtype.ext
    change toLex (Surreal.HahnSeries.workspaceEmbedding (exponentHahnMap e) (exponentHahnMap_strictMono e) (ofLex F.val * ofLex G.val)) = _
    rw [map_mul]; rfl

@[simp] theorem coeff_mapExponents (e : SignSequence.{u} ≃+o SignSequence.{u})
    (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    coeff (mapExponents e F) (e a) = coeff F a := by
  change (Surreal.HahnSeries.workspaceEmbedding (exponentHahnMap e) (exponentHahnMap_strictMono e) (ofLex F.val)).coeff
    (OrderDual.toDual (toSurreal (e a))) = _
  rw [← exponentHahnMap_toSurreal]
  exact Surreal.HahnSeries.workspaceEmbedding_coeff _ _ _ _

theorem mapExponents_inverse (e : SignSequence.{u} ≃+o SignSequence.{u})
    (F : SmallNormalForm.{u}) : mapExponents e.symm (mapExponents e F) = F := by
  apply ext
  intro a
  rw [← e.symm_apply_apply a, coeff_mapExponents, coeff_mapExponents, e.symm_apply_apply]

/-- Ordered exponent automorphisms induce genuine automorphisms of the small formal field. -/
def exponentRingEquiv (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    SmallNormalForm.{u} ≃+* SmallNormalForm.{u} where
  __ := mapExponents e
  invFun := mapExponents e.symm
  left_inv := mapExponents_inverse e
  right_inv F := by simpa using mapExponents_inverse e.symm F

@[simp] theorem exponentRingEquiv_single (e : SignSequence.{u} ≃+o SignSequence.{u})
    (a : SignSequence.{u}) (r : ℝ) : exponentRingEquiv e (single a r) = single (e a) r := by
  apply ext
  intro b
  obtain ⟨c, rfl⟩ := e.surjective b
  change coeff (mapExponents e (single a r)) (e c) = _
  rw [coeff_mapExponents, coeff_single, coeff_single]
  congr 1
  exact propext e.injective.eq_iff.symm

end
end Surreal.Foundations.SmallNormalForm

namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Exponent substitution evaluated in the actual surreal field. -/
def exponentAutomorphism (e : SignSequence.{u} ≃+o SignSequence.{u}) :
    SignSequence.{u} ≃+* SignSequence.{u} :=
  SmallNormalForm.cutEvaluationRingEquiv.symm.trans
    ((SmallNormalForm.exponentRingEquiv e).trans SmallNormalForm.cutEvaluationRingEquiv)

@[simp] theorem normalForm_exponentAutomorphism
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (x : SignSequence.{u}) :
    SmallNormalForm.normalForm (exponentAutomorphism e x) =
      SmallNormalForm.exponentRingEquiv e (SmallNormalForm.normalForm x) :=
  SmallNormalForm.normalForm_cutEvaluation _

@[simp] theorem exponentAutomorphism_ofReal
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (r : ℝ) :
    exponentAutomorphism e (ofReal r) = ofReal r := by
  apply SmallNormalForm.cutEvaluationRingEquiv.symm.injective
  change SmallNormalForm.normalForm _ = SmallNormalForm.normalForm _
  simp only [normalForm_exponentAutomorphism, SmallNormalForm.normalForm_ofReal,
    SmallNormalForm.exponentRingEquiv_single, map_zero]

@[simp] theorem exponentAutomorphism_omegaPower
    (e : SignSequence.{u} ≃+o SignSequence.{u}) (a : SignSequence.{u}) :
    exponentAutomorphism e (omegaPower a) = omegaPower (e a) := by
  apply SmallNormalForm.cutEvaluationRingEquiv.symm.injective
  change SmallNormalForm.normalForm _ = SmallNormalForm.normalForm _
  simp only [normalForm_exponentAutomorphism, SmallNormalForm.normalForm_omegaPower,
    SmallNormalForm.exponentRingEquiv_single]

end
end Surreal.Foundations.SignSequence
