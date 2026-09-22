import Surreal.Foundations.SignSequenceStrongSummation

/-!
# Algebra of actual strong sums

Canonical normal forms preserve ring operations. The native Hahn family
operations therefore prove closure of actual strong summability under
addition, negation, products of independently indexed families, and
multiplication by a fixed actual surreal. For small index types, the
corresponding strong sums obey the same algebraic laws.
-/

universe u v w

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Canonical extraction as a ring map to the native full Hahn carrier. -/
def rawNormalFormRingHom :
    SignSequence.{u} →+* _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℝ where
  toFun := rawNormalForm
  map_zero' := by simp only [rawNormalForm, SmallNormalForm.normalForm_zero]; rfl
  map_one' := by simp only [rawNormalForm, SmallNormalForm.normalForm_one]; rfl
  map_add' x y := by rw [rawNormalForm, SmallNormalForm.normalForm_add]; rfl
  map_mul' x y := by rw [rawNormalForm, SmallNormalForm.normalForm_mul]; rfl

@[simp] theorem rawNormalFormRingHom_apply (x : SignSequence.{u}) :
    rawNormalFormRingHom x = rawNormalForm x := rfl

theorem rawNormalForm_injective : Function.Injective rawNormalForm.{u} := by
  intro x y h
  apply SmallNormalForm.cutEvaluationRingEquiv.symm.injective
  exact Subtype.ext (ofLex.injective h)

@[simp] theorem rawNormalForm_zero : rawNormalForm (0 : SignSequence.{u}) = 0 :=
  rawNormalFormRingHom.map_zero

@[simp] theorem rawNormalForm_one : rawNormalForm (1 : SignSequence.{u}) = 1 :=
  rawNormalFormRingHom.map_one

@[simp] theorem rawNormalForm_add (x y : SignSequence.{u}) :
    rawNormalForm (x + y) = rawNormalForm x + rawNormalForm y :=
  rawNormalFormRingHom.map_add x y

@[simp] theorem rawNormalForm_neg (x : SignSequence.{u}) :
    rawNormalForm (-x) = -rawNormalForm x := rawNormalFormRingHom.map_neg x

@[simp] theorem rawNormalForm_sub (x y : SignSequence.{u}) :
    rawNormalForm (x - y) = rawNormalForm x - rawNormalForm y :=
  rawNormalFormRingHom.map_sub x y

@[simp] theorem rawNormalForm_mul (x y : SignSequence.{u}) :
    rawNormalForm (x * y) = rawNormalForm x * rawNormalForm y :=
  rawNormalFormRingHom.map_mul x y

@[simp] theorem rawNormalForm_pow (x : SignSequence.{u}) (n : ℕ) :
    rawNormalForm (x ^ n) = rawNormalForm x ^ n := rawNormalFormRingHom.map_pow x n

/-- A native family with exactly the canonical terms certifies actual summability. -/
theorem stronglySummable_of_hahnFamily {ι : Type v} {f : ι → SignSequence.{u}}
    (s : _root_.HahnSeries.SummableFamily (_root_.Surreal.{u}ᵒᵈ) ℝ ι)
    (hs : ∀ i, s i = rawNormalForm (f i)) : StronglySummable f := by
  constructor
  · simpa only [hs] using s.isPWO_iUnion_support
  · intro a
    simpa only [hs, Function.HasFiniteSupport, Function.support] using s.finite_co_support a

variable {ι : Type v} {κ : Type w} {f g : ι → SignSequence.{u}}

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
theorem StronglySummable.mul {g : κ → SignSequence.{u}}
    (hf : StronglySummable f) (hg : StronglySummable g) :
    StronglySummable (fun p : ι × κ => f p.1 * g p.2) :=
  stronglySummable_of_hahnFamily
    (_root_.HahnSeries.SummableFamily.mul hf.toHahnFamily hg.toHahnFamily)
    (fun p => (rawNormalForm_mul (f p.1) (g p.2)).symm)

/-- Multiplication by any fixed actual surreal preserves strong summability. -/
theorem StronglySummable.const_mul (hf : StronglySummable f) (x : SignSequence.{u}) :
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
theorem strongSum_mul [Small.{u} κ] {g : κ → SignSequence.{u}}
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

/-- Every actual surreal scalar can be moved outside a small strong sum. -/
theorem strongSum_const_mul (hf : StronglySummable f) (x : SignSequence.{u}) :
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

end Surreal.Foundations.SignSequence
