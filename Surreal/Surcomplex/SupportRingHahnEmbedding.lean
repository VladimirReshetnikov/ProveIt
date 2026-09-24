import Surreal.Surcomplex.NormalFormDegree
import Surreal.Surcomplex.StrongAlgebra
import Surreal.Surcomplex.StrongConstants
import Surreal.HahnSeries.NonpositiveSupportUnits
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Canonical support-ring embeddings into Hahn series

The bridge for transferring `odg:def:prop:support` to the actual carriers.
These are injective maps of the existing normal forms, not assertions
that every Hahn series belongs to an actual surreal universe.
-/

universe u
namespace Surreal

open Foundations
open scoped Pointwise

noncomputable section

namespace Foundations.SignSequence

/-- Growth indices as an additive equivalence; the target uses the dual order for Hahn series. -/
def growthExponentEquiv : SignSequence.{u} ≃+ _root_.Surreal.{u}ᵒᵈ := toSurrealAddEquiv

/-- Reindexing the canonical Hahn support recovers the original Conway support. -/
theorem growthSupport_image (x : SignSequence.{u}) :
    growthExponentEquiv.symm '' (rawNormalForm x).support =
      SmallNormalForm.support (SmallNormalForm.normalForm x) := by
  ext a
  constructor
  · rintro ⟨g, hg, ha⟩
    have he : g = growthExponentEquiv a := by rw [← ha, AddEquiv.apply_symm_apply]
    subst g
    exact hg
  · intro ha
    exact ⟨growthExponentEquiv a, ha, growthExponentEquiv.symm_apply_apply a⟩

/-- Reindexing commutes with every finite sumset in the witness support bound. -/
theorem growthSumsets_image (S : Set (_root_.Surreal.{u}ᵒᵈ)) (d : ℕ) :
    growthExponentEquiv.symm '' (⋃ j ≤ d, j • (S ∪ {0})) =
      ⋃ j ≤ d, j • (growthExponentEquiv.symm '' S ∪ {0}) := by
  simp only [Set.image_iUnion, Set.image_nsmul, Set.image_union, Set.image_singleton, map_zero]

/-- Actual leading growth is the order of the canonical series in the dual exponent order. -/
theorem rawNormalForm_order (x : SignSequence.{u}) :
    (rawNormalForm x).order = OrderDual.toDual (toSurreal (leadingExponent x)) := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : rawNormalForm x ≠ 0 := by
    intro h
    exact hx (rawNormalForm_injective (h.trans rawNormalForm_zero.symm))
  have ho : (rawNormalForm x).orderTop =
      ((OrderDual.toDual (toSurreal (leadingExponent x)) : _root_.Surreal.{u}ᵒᵈ) :
        WithTop (_root_.Surreal.{u}ᵒᵈ)) := by
    apply _root_.HahnSeries.orderTop_eq_of_le
    · exact leadingExponent_mem_normalForm hx
    · intro b hb
      obtain ⟨c, hc⟩ := toSurreal_surjective (OrderDual.ofDual b)
      have hc' : OrderDual.toDual (toSurreal c) = b := congrArg OrderDual.toDual hc
      rw [← hc'] at hb ⊢
      exact (toSurreal_le_iff c (leadingExponent x)).mpr
        (normalForm_support_le_leadingExponent x hb)
  rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hn] at ho
  exact WithTop.coe_injective ho

/-- The actual real support ring maps into its canonical Hahn support ring. -/
def supportHahnEmbedding : nonnegativeSupportSubring.{u} →+*
    HahnSeries.nonpositiveSupportSubring (_root_.Surreal.{u}ᵒᵈ) ℝ :=
  (normalFormHahnHom.comp nonnegativeSupportSubring.subtype).codRestrict _ (fun x => x.property)

theorem supportHahnEmbedding_injective : Function.Injective supportHahnEmbedding.{u} := by
  intro x y h
  apply Subtype.ext
  have he : (supportHahnEmbedding x).val = (supportHahnEmbedding y).val :=
    congrArg (fun p : HahnSeries.nonpositiveSupportSubring (_root_.Surreal.{u}ᵒᵈ) ℝ => p.val) h
  exact rawNormalForm_injective he

@[simp] theorem supportHahnEmbedding_constant (r : ℝ) :
    supportHahnEmbedding (realConstants.{u} r) = HahnSeries.nonpositiveConstants r := by
  apply Subtype.ext
  exact rawNormalForm_ofReal r

@[simp] theorem supportHahnEmbedding_constantCoeff (x : nonnegativeSupportSubring.{u}) :
    HahnSeries.nonpositiveConstantCoeff (supportHahnEmbedding x) = constantCoeff x := rfl

theorem supportHahnEmbedding_nonconstant (x : nonnegativeSupportSubring.{u})
    (hx : x ≠ realConstants (constantCoeff x)) :
    supportHahnEmbedding x ≠ HahnSeries.nonpositiveConstants
      (HahnSeries.nonpositiveConstantCoeff (supportHahnEmbedding x)) := by
  rw [supportHahnEmbedding_constantCoeff, ← supportHahnEmbedding_constant]
  exact supportHahnEmbedding_injective.ne hx

/-- A nonconstant actual support-ring element has strictly positive leading growth. -/
theorem nonnegativeSupport_leadingExponent_pos (x : nonnegativeSupportSubring.{u})
    (hx : x ≠ realConstants (constantCoeff x)) : 0 < leadingExponent x.val := by
  have ho : (rawNormalForm x.val).order < 0 := lt_of_not_ge (fun h =>
    supportHahnEmbedding_nonconstant x hx
      (HahnSeries.nonpositiveSupport_eq_constant_of_order_nonneg (supportHahnEmbedding x) h))
  rw [rawNormalForm_order] at ho
  change 0 < toSurreal (leadingExponent x.val) at ho
  exact (toSurreal_lt_iff 0 _).mp (by simpa only [toSurreal_zero] using ho)

/-- Equalities of Hahn degrees become equalities of the actual leading growth exponents. -/
theorem leadingExponent_eq_of_hahnDegree (x y : nonnegativeSupportSubring.{u}) (n : ℕ)
    (h : HahnSeries.nonpositiveDegree (supportHahnEmbedding x) =
      n • HahnSeries.nonpositiveDegree (supportHahnEmbedding y)) :
    leadingExponent x.val = n • leadingExponent y.val := by
  change -(rawNormalForm x.val).order = n • -(rawNormalForm y.val).order at h
  rw [rawNormalForm_order, rawNormalForm_order] at h
  have he : -toSurreal (leadingExponent x.val) = n • -toSurreal (leadingExponent y.val) :=
    congrArg OrderDual.ofDual h
  rw [smul_neg, neg_inj] at he
  apply (toSurreal_inj _ _).mp
  change toSurrealAddHom (leadingExponent x.val) = toSurrealAddHom (n • leadingExponent y.val)
  rw [map_nsmul]
  exact he

end Foundations.SignSequence

namespace Surcomplex

/-- The support of the actual complex Conway normal form, indexed by actual growth exponents. -/
def growthSupport (z : Surcomplex.{u}) : Set SignSequence.{u} := {a | growthCoeff z a ≠ 0}

/-- The actual complex support is the reindexing of its canonical Hahn support. -/
theorem growthSupport_image (z : Surcomplex.{u}) :
    SignSequence.growthExponentEquiv.symm '' (rawNormalForm z).support = growthSupport z := by
  ext a
  constructor
  · rintro ⟨g, hg, ha⟩
    have he : g = SignSequence.growthExponentEquiv a := by rw [← ha, AddEquiv.apply_symm_apply]
    subst g
    exact hg
  · intro ha
    exact ⟨SignSequence.growthExponentEquiv a, ha,
      SignSequence.growthExponentEquiv.symm_apply_apply a⟩

/-- The complex leading growth exponent is the order of the canonical complex normal form. -/
theorem rawNormalForm_order (z : Surcomplex.{u}) :
    (rawNormalForm z).order = OrderDual.toDual (SignSequence.toSurreal (leadingExponent z)) := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : rawNormalForm z ≠ 0 := by
    intro h
    exact hz (rawNormalForm_injective (h.trans rawNormalForm_zero.symm))
  have ho : (rawNormalForm z).orderTop =
      ((OrderDual.toDual (SignSequence.toSurreal (leadingExponent z)) : _root_.Surreal.{u}ᵒᵈ) :
        WithTop (_root_.Surreal.{u}ᵒᵈ)) := by
    apply _root_.HahnSeries.orderTop_eq_of_le
    · change growthCoeff z (leadingExponent z) ≠ 0
      rw [growthCoeff_leadingExponent]
      exact leadingCoeff_ne_zero hz
    · intro b hb
      obtain ⟨c, hc⟩ := SignSequence.toSurreal_surjective (OrderDual.ofDual b)
      have hc' : OrderDual.toDual (SignSequence.toSurreal c) = b := congrArg OrderDual.toDual hc
      rw [← hc'] at hb ⊢
      exact (SignSequence.toSurreal_le_iff c (leadingExponent z)).mpr
        (growthCoeff_leading_bound z c hb)
  rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hn] at ho
  exact WithTop.coe_injective ho

/-- The actual complex support ring embeds in its canonical complex Hahn support ring. -/
def supportHahnEmbedding : nonnegativeSupportSubring.{u} →+*
    HahnSeries.nonpositiveSupportSubring (_root_.Surreal.{u}ᵒᵈ) ℂ :=
  (rawNormalFormRingHom.comp nonnegativeSupportSubring.subtype).codRestrict _ (by
    intro z a ha
    change (rawNormalForm z.val).coeff a = 0
    rw [coeff_rawNormalForm]
    apply Complex.ext
    · exact z.property.1 a ha
    · exact z.property.2 a ha)

theorem supportHahnEmbedding_injective : Function.Injective supportHahnEmbedding.{u} := by
  intro x y h
  apply Subtype.ext
  exact rawNormalForm_injective (congrArg Subtype.val h)

@[simp] theorem supportHahnEmbedding_constant (c : ℂ) :
    supportHahnEmbedding (complexConstants.{u} c) = HahnSeries.nonpositiveConstants c := by
  apply Subtype.ext
  exact rawNormalForm_ofComplex c

@[simp] theorem supportHahnEmbedding_constantCoeff (z : nonnegativeSupportSubring.{u}) :
    HahnSeries.nonpositiveConstantCoeff (supportHahnEmbedding z) = constantCoeff z := by
  change (rawNormalForm z.val).coeff 0 = constantCoeff z
  rw [coeff_rawNormalForm]
  rfl

theorem supportHahnEmbedding_nonconstant (z : nonnegativeSupportSubring.{u})
    (hz : z ≠ complexConstants (constantCoeff z)) :
    supportHahnEmbedding z ≠ HahnSeries.nonpositiveConstants
      (HahnSeries.nonpositiveConstantCoeff (supportHahnEmbedding z)) := by
  rw [supportHahnEmbedding_constantCoeff, ← supportHahnEmbedding_constant]
  exact supportHahnEmbedding_injective.ne hz

/-- A nonconstant actual complex support-ring element has strictly positive leading growth. -/
theorem nonnegativeSupport_leadingExponent_pos (z : nonnegativeSupportSubring.{u})
    (hz : z ≠ complexConstants (constantCoeff z)) : 0 < leadingExponent z.val := by
  have ho : (rawNormalForm z.val).order < 0 := lt_of_not_ge (fun h =>
    supportHahnEmbedding_nonconstant z hz
      (HahnSeries.nonpositiveSupport_eq_constant_of_order_nonneg (supportHahnEmbedding z) h))
  rw [rawNormalForm_order] at ho
  change 0 < SignSequence.toSurreal (leadingExponent z.val) at ho
  exact (SignSequence.toSurreal_lt_iff 0 _).mp (by simpa only [SignSequence.toSurreal_zero] using ho)

/-- Hahn degree identities reflect to the actual surcomplex leading exponents. -/
theorem leadingExponent_eq_of_hahnDegree (z w : nonnegativeSupportSubring.{u}) (n : ℕ)
    (h : HahnSeries.nonpositiveDegree (supportHahnEmbedding z) =
      n • HahnSeries.nonpositiveDegree (supportHahnEmbedding w)) :
    leadingExponent z.val = n • leadingExponent w.val := by
  change -(rawNormalForm z.val).order = n • -(rawNormalForm w.val).order at h
  rw [rawNormalForm_order, rawNormalForm_order] at h
  have he : -SignSequence.toSurreal (leadingExponent z.val) =
      n • -SignSequence.toSurreal (leadingExponent w.val) := congrArg OrderDual.ofDual h
  rw [smul_neg, neg_inj] at he
  apply (SignSequence.toSurreal_inj _ _).mp
  change SignSequence.toSurrealAddHom (leadingExponent z.val) =
    SignSequence.toSurrealAddHom (n • leadingExponent w.val)
  rw [map_nsmul]
  exact he

end Surcomplex
end
end Surreal
