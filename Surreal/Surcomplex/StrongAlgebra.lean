import Surreal.Surcomplex.StrongSummation
import Surreal.Foundations.SignSequenceStrongAlgebra

/-!
# Algebra of actual complex strong sums

Canonical real-coordinate extraction and the native complex Hahn equivalence
make exact complex normal-form extraction a ring homomorphism. Native Hahn
family operations then establish addition, negation, independent products,
and multiplication by any fixed actual surcomplex scalar. The corresponding
strong-sum identities retain the explicit small-index hypotheses.
-/

universe u v w

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private def coordinateRawNormalFormRingHom : Surcomplex.{u} →+*
    Complexify (_root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℝ) where
  toFun z := ⟨SignSequence.rawNormalFormRingHom z.re, SignSequence.rawNormalFormRingHom z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by
    apply QuadraticAlgebra.ext
    · exact SignSequence.rawNormalFormRingHom.map_one
    · exact SignSequence.rawNormalFormRingHom.map_zero
  map_add' z w := by apply QuadraticAlgebra.ext <;> simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext
    · simp only [Complexify.mul_re, map_sub, map_mul]
    · simp only [Complexify.mul_im, map_add, map_mul]

/-- Canonical complex extraction is a ring map to the native full Hahn carrier. -/
def rawNormalFormRingHom :
    Surcomplex.{u} →+* _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℂ :=
  HahnSeries.realComplexHahnEquiv.toRingHom.comp coordinateRawNormalFormRingHom

@[simp] theorem rawNormalFormRingHom_apply (z : Surcomplex.{u}) :
    rawNormalFormRingHom z = rawNormalForm z := rfl

@[simp] theorem rawNormalForm_zero : rawNormalForm (0 : Surcomplex.{u}) = 0 :=
  rawNormalFormRingHom.map_zero

@[simp] theorem rawNormalForm_one : rawNormalForm (1 : Surcomplex.{u}) = 1 :=
  rawNormalFormRingHom.map_one

@[simp] theorem rawNormalForm_add (x y : Surcomplex.{u}) :
    rawNormalForm (x + y) = rawNormalForm x + rawNormalForm y :=
  rawNormalFormRingHom.map_add x y

@[simp] theorem rawNormalForm_neg (x : Surcomplex.{u}) :
    rawNormalForm (-x) = -rawNormalForm x := rawNormalFormRingHom.map_neg x

@[simp] theorem rawNormalForm_sub (x y : Surcomplex.{u}) :
    rawNormalForm (x - y) = rawNormalForm x - rawNormalForm y :=
  rawNormalFormRingHom.map_sub x y

@[simp] theorem rawNormalForm_mul (x y : Surcomplex.{u}) :
    rawNormalForm (x * y) = rawNormalForm x * rawNormalForm y :=
  rawNormalFormRingHom.map_mul x y

@[simp] theorem rawNormalForm_pow (x : Surcomplex.{u}) (n : ℕ) :
    rawNormalForm (x ^ n) = rawNormalForm x ^ n := rawNormalFormRingHom.map_pow x n

/-- A native family with exactly the canonical terms certifies actual summability. -/
theorem stronglySummable_of_hahnFamily {ι : Type v} {f : ι → Surcomplex.{u}}
    (s : _root_.HahnSeries.SummableFamily (_root_.Surreal.{u}ᵒᵈ) ℂ ι)
    (hs : ∀ i, s i = rawNormalForm (f i)) : StronglySummable f := by
  constructor
  · simpa only [hs] using s.isPWO_iUnion_support
  · intro a
    simpa only [hs, Function.HasFiniteSupport, Function.support] using s.finite_co_support a

variable {ι : Type v} {κ : Type w} {f g : ι → Surcomplex.{u}}

/-- Adding two strongly summable families preserves both support conditions. -/
theorem StronglySummable.add (hf : StronglySummable f) (hg : StronglySummable g) :
    StronglySummable (fun i => f i + g i) :=
  stronglySummable_of_hahnFamily (hf.toHahnFamily + hg.toHahnFamily)
    (fun i => (rawNormalForm_add (f i) (g i)).symm)

/-- Negation preserves strong summability. -/
theorem StronglySummable.neg (hf : StronglySummable f) :
    StronglySummable (fun i => -f i) :=
  stronglySummable_of_hahnFamily (-hf.toHahnFamily)
    (fun i => (rawNormalForm_neg (f i)).symm)

/-- Products are jointly summable over the product of the index types. -/
theorem StronglySummable.mul {g : κ → Surcomplex.{u}}
    (hf : StronglySummable f) (hg : StronglySummable g) :
    StronglySummable (fun p : ι × κ => f p.1 * g p.2) :=
  stronglySummable_of_hahnFamily
    (_root_.HahnSeries.SummableFamily.mul hf.toHahnFamily hg.toHahnFamily)
    (fun p => (rawNormalForm_mul (f p.1) (g p.2)).symm)

/-- Multiplication by any fixed actual surcomplex preserves strong summability. -/
theorem StronglySummable.const_mul (hf : StronglySummable f) (x : Surcomplex.{u}) :
    StronglySummable (fun i => x * f i) := by
  apply stronglySummable_of_hahnFamily (rawNormalForm x • hf.toHahnFamily)
  intro i
  rw [_root_.HahnSeries.SummableFamily.smul_apply,
    _root_.HahnSeries.of_symm_smul_of_eq_mul]
  exact (rawNormalForm_mul x (f i)).symm

section Small

variable [Small.{u} ι]

/-- Actual strong summation is additive. -/
theorem strongSum_add (hf : StronglySummable f) (hg : StronglySummable g) :
    strongSum (fun i => f i + g i) (hf.add hg) = strongSum f hf + strongSum g hg := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_add, rawNormalForm_strongSum,
    rawNormalForm_strongSum]
  have hs : (hf.add hg).toHahnFamily = hf.toHahnFamily + hg.toHahnFamily := by
    apply _root_.HahnSeries.SummableFamily.ext
    intro i
    exact rawNormalForm_add (f i) (g i)
  rw [hs, _root_.HahnSeries.SummableFamily.hsum_add]

/-- Negation commutes with actual strong summation. -/
theorem strongSum_neg (hf : StronglySummable f) :
    strongSum (fun i => -f i) hf.neg = -strongSum f hf := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_neg, rawNormalForm_strongSum]
  have hs : hf.neg.toHahnFamily = -hf.toHahnFamily := by
    apply _root_.HahnSeries.SummableFamily.ext
    intro i
    exact rawNormalForm_neg (f i)
  rw [hs]
  exact map_neg _root_.HahnSeries.SummableFamily.lsum hf.toHahnFamily

/-- The product of strong sums equals the jointly summable double sum. -/
theorem strongSum_mul [Small.{u} κ] {g : κ → Surcomplex.{u}}
    (hf : StronglySummable f) (hg : StronglySummable g) :
    strongSum (fun p : ι × κ => f p.1 * g p.2) (hf.mul hg) =
      strongSum f hf * strongSum g hg := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_mul, rawNormalForm_strongSum,
    rawNormalForm_strongSum]
  have hs : (hf.mul hg).toHahnFamily =
      _root_.HahnSeries.SummableFamily.mul hf.toHahnFamily hg.toHahnFamily := by
    apply _root_.HahnSeries.SummableFamily.ext
    intro p
    exact rawNormalForm_mul (f p.1) (g p.2)
  rw [hs, _root_.HahnSeries.SummableFamily.hsum_mul]

/-- Every actual surcomplex scalar can be moved outside a small strong sum. -/
theorem strongSum_const_mul (hf : StronglySummable f) (x : Surcomplex.{u}) :
    strongSum (fun i => x * f i) (hf.const_mul x) = x * strongSum f hf := by
  apply rawNormalForm_injective
  rw [rawNormalForm_strongSum, rawNormalForm_mul, rawNormalForm_strongSum]
  have hs : (hf.const_mul x).toHahnFamily = rawNormalForm x • hf.toHahnFamily := by
    apply _root_.HahnSeries.SummableFamily.ext
    intro i
    rw [_root_.HahnSeries.SummableFamily.smul_apply,
      _root_.HahnSeries.of_symm_smul_of_eq_mul]
    exact rawNormalForm_mul x (f i)
  rw [hs, _root_.HahnSeries.SummableFamily.hsum_smul]

end Small

end

end Surreal.Surcomplex
