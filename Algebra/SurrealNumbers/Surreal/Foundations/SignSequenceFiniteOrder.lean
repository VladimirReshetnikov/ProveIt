import Surreal.Foundations.SignSequenceFiniteNormalForm
import Surreal.HahnSeries.FiniteSupport
import Mathlib.Algebra.Order.Hom.Ring

/-!
# Arithmetic and order of finite actual normal forms

Finite monomial evaluation preserves and reflects equality and the full
lexicographic Hahn order. It identifies the subring of finite-support Hahn
series with the subring of actual sign-sequence numbers represented by these
finite normal forms. No infinite summation or infinite-support embedding is
assumed here.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

open Surreal.HahnSeries

variable {Γ : Type v} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ]

omit [IsOrderedCancelAddMonoid Γ] in
/-- Equality of actual finite normal forms is equality of their coefficients. -/
theorem finiteMonomialEvaluation_eq_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F G : AddMonoidAlgebra ℝ Γ) :
    finiteMonomialEvaluation e F = finiteMonomialEvaluation e G ↔ F = G :=
  (finiteMonomialEvaluation_injective e he).eq_iff

/-- Strict comparison of actual finite normal forms is precisely the Hahn comparison. -/
theorem finiteMonomialEvaluation_lt_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F G : AddMonoidAlgebra ℝ Γ) :
    finiteMonomialEvaluation e F < finiteMonomialEvaluation e G ↔
      toLex (finiteSupportEmbedding F) < toLex (finiteSupportEmbedding G) := by
  have h := finiteMonomialEvaluation_pos_iff e he (G - F)
  rw [map_sub, ← finiteSupportEmbedding_eq_ofFinsupp, map_sub, toLex_sub,
    sub_pos, sub_pos] at h
  exact h

/-- Non-strict comparison is preserved and reflected as well. -/
theorem finiteMonomialEvaluation_le_iff (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F G : AddMonoidAlgebra ℝ Γ) :
    finiteMonomialEvaluation e F ≤ finiteMonomialEvaluation e G ↔
      toLex (finiteSupportEmbedding F) ≤ toLex (finiteSupportEmbedding G) := by
  simpa only [not_lt] using (finiteMonomialEvaluation_lt_iff e he G F).not

/-- The first coefficient at which two finite forms differ decides their order. -/
theorem finiteMonomialEvaluation_lt_iff_coeff (e : Γ →+ SignSequence.{u})
    (he : StrictMono e) (F G : AddMonoidAlgebra ℝ Γ) :
    finiteMonomialEvaluation e F < finiteMonomialEvaluation e G ↔
      ∃ g : Γ, (∀ h : Γ, h < g → F.coeff h = G.coeff h) ∧ F.coeff g < G.coeff g := by
  rw [finiteMonomialEvaluation_lt_iff e he, _root_.HahnSeries.lt_iff]
  simp only [ofLex_toLex, coeff_finiteSupportEmbedding]

/-- The finite coefficient ring viewed in lexicographically ordered Hahn series. -/
def finiteSupportLexEmbedding : AddMonoidAlgebra ℝ Γ →+* Lex (_root_.HahnSeries Γ ℝ) where
  toFun F := toLex (finiteSupportEmbedding F)
  map_zero' := by simp
  map_one' := by simp
  map_add' F G := by simp
  map_mul' F G := by simp

@[simp] theorem finiteSupportLexEmbedding_apply (F : AddMonoidAlgebra ℝ Γ) :
    finiteSupportLexEmbedding F = toLex (finiteSupportEmbedding F) := rfl

/-- The Hahn subring consisting exactly of finite-support series, with its native order. -/
def finiteHahnSubring (Γ : Type v) [AddCommMonoid Γ] [LinearOrder Γ]
    [IsOrderedCancelAddMonoid Γ] : Subring (Lex (_root_.HahnSeries Γ ℝ)) :=
  (finiteSupportLexEmbedding : AddMonoidAlgebra ℝ Γ →+* Lex (_root_.HahnSeries Γ ℝ)).range

@[simp] theorem mem_finiteHahnSubring (x : Lex (_root_.HahnSeries Γ ℝ)) :
    x ∈ finiteHahnSubring Γ ↔ (ofLex x).support.Finite := by
  change (∃ F, toLex (finiteSupportEmbedding F) = x) ↔ _
  rw [← mem_range_finiteSupportEmbedding]
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F, congrArg ofLex hF⟩
  · rintro ⟨F, hF⟩
    exact ⟨F, congrArg toLex hF⟩

/-- The actual sign-sequence subring represented by the given finite exponent forms. -/
def finiteMonomialSubring (e : Γ →+ SignSequence.{u}) : Subring SignSequence.{u} :=
  (finiteMonomialEvaluation e).range

private def finiteHahnPresentation : AddMonoidAlgebra ℝ Γ ≃+* finiteHahnSubring Γ :=
  RingEquiv.ofBijective (finiteSupportLexEmbedding (Γ := Γ)).rangeRestrict
    ⟨fun _ _ h => finiteSupportEmbedding_injective
      (congrArg (fun x : finiteHahnSubring Γ => ofLex x.val) h),
      (finiteSupportLexEmbedding (Γ := Γ)).rangeRestrict_surjective⟩

private def finiteMonomialPresentation (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    AddMonoidAlgebra ℝ Γ ≃+* finiteMonomialSubring e :=
  RingEquiv.ofBijective (finiteMonomialEvaluation e).rangeRestrict
    ⟨fun _ _ h => finiteMonomialEvaluation_injective e he (congrArg Subtype.val h),
      (finiteMonomialEvaluation e).rangeRestrict_surjective⟩

/-- Finite-support Hahn arithmetic and actual finite normal-form arithmetic agree. -/
def finiteHahnRingEquiv (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    finiteHahnSubring Γ ≃+* finiteMonomialSubring e :=
  finiteHahnPresentation.symm.trans (finiteMonomialPresentation e he)

/-- On a specified finite coefficient expression, the equivalence is ordinary evaluation. -/
@[simp] theorem finiteHahnRingEquiv_apply (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (F : AddMonoidAlgebra ℝ Γ) :
    (finiteHahnRingEquiv e he ((finiteSupportLexEmbedding (Γ := Γ)).rangeRestrict F) :
      SignSequence.{u}) = finiteMonomialEvaluation e F := by
  change ((finiteMonomialPresentation e he)
    (finiteHahnPresentation.symm (finiteHahnPresentation F)) : SignSequence.{u}) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

/-- The finite normal-form identification is an isomorphism of ordered rings. -/
def finiteHahnOrderRingEquiv (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    finiteHahnSubring Γ ≃+*o finiteMonomialSubring e where
  __ := finiteHahnRingEquiv e he
  map_le_map_iff' := by
    intro x y
    obtain ⟨F, rfl⟩ := (finiteSupportLexEmbedding (Γ := Γ)).rangeRestrict_surjective x
    obtain ⟨G, rfl⟩ := (finiteSupportLexEmbedding (Γ := Γ)).rangeRestrict_surjective y
    change (finiteHahnRingEquiv e he ((finiteSupportLexEmbedding (Γ := Γ)).rangeRestrict F) :
      SignSequence.{u}) ≤
      (finiteHahnRingEquiv e he ((finiteSupportLexEmbedding (Γ := Γ)).rangeRestrict G) :
        SignSequence.{u}) ↔ toLex (finiteSupportEmbedding F) ≤ toLex (finiteSupportEmbedding G)
    rw [finiteHahnRingEquiv_apply, finiteHahnRingEquiv_apply]
    exact finiteMonomialEvaluation_le_iff e he F G

/-- The finite Hahn subring embeds in the full actual sign field with its order. -/
def finiteHahnOrderEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    finiteHahnSubring Γ ↪o SignSequence.{u} :=
  (finiteHahnOrderRingEquiv e he).toOrderIso.toOrderEmbedding.trans
    (OrderEmbedding.subtype (fun x : SignSequence.{u} => x ∈ finiteMonomialSubring e))

@[simp] theorem finiteHahnOrderEmbedding_apply (e : Γ →+ SignSequence.{u})
    (he : StrictMono e) (F : AddMonoidAlgebra ℝ Γ) :
    finiteHahnOrderEmbedding e he ((finiteSupportLexEmbedding (Γ := Γ)).rangeRestrict F) =
      finiteMonomialEvaluation e F := finiteHahnRingEquiv_apply e he F

end

end Surreal.Foundations.SignSequence
