import Surreal.HahnSeries.MultiplierTransfer
import Surreal.Surcomplex.SupportRingHahnEmbedding
import Surreal.Foundations.OmnificSupportBounds
import Surreal.Surcomplex.GaussianOmnificIntegers

/-!
# Multipliers of the actual purely infinite ideals

The actual-carrier assertions of `odg:def:thm:multiplier` and
`odg:def:eq:multiplier`. Quantifiers range over the actual surreal and
surcomplex fields, using only monomial preimages in their normal forms.
-/

universe u
namespace Surreal

open Foundations

noncomputable section

namespace Foundations.SignSequence

/-- An actual monomial has its literal one-term canonical Hahn series. -/
theorem rawNormalForm_omegaPower (a : SignSequence.{u}) :
    rawNormalForm (omegaPower a) = _root_.HahnSeries.single (OrderDual.toDual (toSurreal a)) 1 := by
  rw [rawNormalForm, SmallNormalForm.normalForm_omegaPower]
  apply _root_.HahnSeries.ext
  funext b
  change (_root_.SurrealHahnSeries.single (toSurreal a) 1).coeff (OrderDual.ofDual b) = _
  simp only [_root_.SurrealHahnSeries.coeff_single, Pi.single_apply, _root_.HahnSeries.coeff_single]
  congr 1

/-- The actual image of the real purely infinite ideal, expressed by canonical coefficients. -/
def IsPurelyInfinite (x : SignSequence.{u}) : Prop := HahnSeries.PurelyInfiniteSeries (rawNormalForm x)

/-- This coefficient predicate is precisely membership in the existing actual ideal. -/
theorem isPurelyInfinite_iff (x : nonnegativeSupportSubring.{u}) :
    IsPurelyInfinite x.val ↔ x ∈ purelyInfiniteIdeal :=
  HahnSeries.purelyInfiniteSeries_iff (supportHahnEmbedding x)

theorem IsPurelyInfinite.mem_supportRing {x : SignSequence.{u}} (hx : IsPurelyInfinite x) :
    x ∈ nonnegativeSupportSubring := HahnSeries.PurelyInfiniteSeries.mem_supportRing hx

/-- The multiplier condition with both quantifiers in the actual surreal field. -/
def IsPurelyInfiniteMultiplier (x : SignSequence.{u}) : Prop :=
  ∀ y : SignSequence.{u}, IsPurelyInfinite y → IsPurelyInfinite (x * y)

/-- The multiplier predicate is exactly multiplication preserving the existing native ideal. -/
theorem purelyInfiniteMultiplier_iff_ideal (x : SignSequence.{u}) :
    IsPurelyInfiniteMultiplier x ↔
      ∀ y : nonnegativeSupportSubring.{u}, y ∈ purelyInfiniteIdeal →
        ∃ w : nonnegativeSupportSubring.{u}, w ∈ purelyInfiniteIdeal ∧ x * y.val = w.val := by
  constructor
  · intro h y hy
    have hp := h y.val ((isPurelyInfinite_iff y).mpr hy)
    let w : nonnegativeSupportSubring.{u} := ⟨x * y.val, hp.mem_supportRing⟩
    exact ⟨w, (isPurelyInfinite_iff w).mp hp, rfl⟩
  · intro h y hy
    let y' : nonnegativeSupportSubring.{u} := ⟨y, hy.mem_supportRing⟩
    obtain ⟨w, hw, he⟩ := h y' ((isPurelyInfinite_iff y').mp hy)
    change x * y = w.val at he
    rw [he]
    exact (isPurelyInfinite_iff w).mpr hw

/-- The actual real support ring is exactly the multiplier ring of the actual ideal. -/
theorem purelyInfiniteMultiplier_iff (x : SignSequence.{u}) :
    IsPurelyInfiniteMultiplier x ↔ x ∈ nonnegativeSupportSubring := by
  apply HahnSeries.multiplier_pullback_iff normalFormHahnHom ?_ x
  intro g _
  obtain ⟨a, ha⟩ := toSurreal_surjective (OrderDual.ofDual g)
  refine ⟨omegaPower a, ?_⟩
  change rawNormalForm (omegaPower a) = _
  rw [rawNormalForm_omegaPower, ha]
  rfl

/-- Real constants are zero together with the invertible actual multipliers. -/
theorem real_iff_multiplier_and_inverse (x : SignSequence.{u}) :
    (∃ r : ℝ, x = ofReal r) ↔
      x = 0 ∨ (x ≠ 0 ∧ IsPurelyInfiniteMultiplier x ∧ IsPurelyInfiniteMultiplier x⁻¹) := by
  rw [purelyInfiniteMultiplier_iff, purelyInfiniteMultiplier_iff]
  exact HahnSeries.coefficient_pullback_iff normalFormHahnHom ofReal.toRingHom rawNormalForm_ofReal x

end Foundations.SignSequence
namespace Surcomplex

/-- A real Conway monomial has the same one-term complex normal form. -/
theorem rawNormalForm_real_omegaPower (a : SignSequence.{u}) :
    rawNormalForm (ofReal (SignSequence.omegaPower a)) =
      _root_.HahnSeries.single (OrderDual.toDual (SignSequence.toSurreal a)) 1 := by
  apply _root_.HahnSeries.ext
  funext b
  rw [coeff_rawNormalForm, ofReal_re, ofReal_im, SignSequence.rawNormalForm_omegaPower,
    SignSequence.rawNormalForm_zero]
  by_cases hb : b = OrderDual.toDual (SignSequence.toSurreal a)
  · subst b; simp only [_root_.HahnSeries.coeff_single_same, _root_.HahnSeries.coeff_zero]; rfl
  · simp only [_root_.HahnSeries.coeff_single_of_ne hb, _root_.HahnSeries.coeff_zero]; rfl

/-- The actual complex purely infinite predicate. -/
def IsPurelyInfinite (z : Surcomplex.{u}) : Prop := HahnSeries.PurelyInfiniteSeries (rawNormalForm z)

theorem isPurelyInfinite_iff (z : nonnegativeSupportSubring.{u}) :
    IsPurelyInfinite z.val ↔ z ∈ purelyInfiniteIdeal := by
  rw [IsPurelyInfinite, HahnSeries.PurelyInfiniteSeries]
  change (∀ a, 0 ≤ a → (rawNormalForm z.val).coeff a = 0) ↔ constantCoeff z = 0
  constructor
  · intro h
    exact (supportHahnEmbedding_constantCoeff z).symm.trans (h 0 le_rfl)
  · intro h a ha
    rcases eq_or_lt_of_le ha with he | he
    · subst a
      exact (supportHahnEmbedding_constantCoeff z).trans h
    · exact (supportHahnEmbedding z).property a he

/-- Support membership is reflected by the complex normal-form embedding. -/
theorem mem_supportRing_iff_rawNormalForm (z : Surcomplex.{u}) :
    z ∈ nonnegativeSupportSubring ↔
      rawNormalForm z ∈ HahnSeries.nonpositiveSupportSubring (_root_.Surreal.{u}ᵒᵈ) ℂ := by
  constructor
  · intro hz; exact (supportHahnEmbedding ⟨z, hz⟩).property
  · intro hz
    constructor
    · intro a ha
      have h := congrArg Complex.re (hz a ha)
      change (SignSequence.rawNormalForm z.re).coeff a = 0
      simpa only [coeff_rawNormalForm, Complex.zero_re] using h
    · intro a ha
      have h := congrArg Complex.im (hz a ha)
      change (SignSequence.rawNormalForm z.im).coeff a = 0
      simpa only [coeff_rawNormalForm, Complex.zero_im] using h

theorem IsPurelyInfinite.mem_supportRing {z : Surcomplex.{u}} (hz : IsPurelyInfinite z) :
    z ∈ nonnegativeSupportSubring :=
  (mem_supportRing_iff_rawNormalForm z).mpr (HahnSeries.PurelyInfiniteSeries.mem_supportRing hz)

/-- Multiplication is tested only on actual purely infinite surcomplex numbers. -/
def IsPurelyInfiniteMultiplier (z : Surcomplex.{u}) : Prop :=
  ∀ w : Surcomplex.{u}, IsPurelyInfinite w → IsPurelyInfinite (z * w)

/-- The multiplier predicate is exactly multiplication preserving the existing native ideal. -/
theorem purelyInfiniteMultiplier_iff_ideal (z : Surcomplex.{u}) :
    IsPurelyInfiniteMultiplier z ↔
      ∀ y : nonnegativeSupportSubring.{u}, y ∈ purelyInfiniteIdeal →
        ∃ w : nonnegativeSupportSubring.{u}, w ∈ purelyInfiniteIdeal ∧ z * y.val = w.val := by
  constructor
  · intro h y hy
    have hp := h y.val ((isPurelyInfinite_iff y).mpr hy)
    let w : nonnegativeSupportSubring.{u} := ⟨z * y.val, hp.mem_supportRing⟩
    exact ⟨w, (isPurelyInfinite_iff w).mp hp, rfl⟩
  · intro h y hy
    let y' : nonnegativeSupportSubring.{u} := ⟨y, hy.mem_supportRing⟩
    obtain ⟨w, hw, he⟩ := h y' ((isPurelyInfinite_iff y').mp hy)
    change z * y = w.val at he
    rw [he]
    exact (isPurelyInfinite_iff w).mpr hw

/-- The actual complex support ring is exactly the multiplier ring of its purely infinite ideal. -/
theorem purelyInfiniteMultiplier_iff (z : Surcomplex.{u}) :
    IsPurelyInfiniteMultiplier z ↔ z ∈ nonnegativeSupportSubring := by
  rw [mem_supportRing_iff_rawNormalForm]
  apply HahnSeries.multiplier_pullback_iff rawNormalFormRingHom ?_ z
  intro g _
  obtain ⟨a, ha⟩ := SignSequence.toSurreal_surjective (OrderDual.ofDual g)
  refine ⟨ofReal (SignSequence.omegaPower a), ?_⟩
  change rawNormalForm _ = _
  rw [rawNormalForm_real_omegaPower, ha]
  rfl

/-- Ordinary complex coefficients are recovered as zero or invertible actual multipliers. -/
theorem complex_iff_multiplier_and_inverse (z : Surcomplex.{u}) :
    (∃ c : ℂ, z = ofComplex c) ↔
      z = 0 ∨ (z ≠ 0 ∧ IsPurelyInfiniteMultiplier z ∧ IsPurelyInfiniteMultiplier z⁻¹) := by
  rw [purelyInfiniteMultiplier_iff, purelyInfiniteMultiplier_iff,
    mem_supportRing_iff_rawNormalForm, mem_supportRing_iff_rawNormalForm]
  exact HahnSeries.coefficient_pullback_iff rawNormalFormRingHom ofComplex rawNormalForm_ofComplex z

end Surcomplex
end
end Surreal
