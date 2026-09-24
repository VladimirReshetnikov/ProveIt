import Surreal.Foundations.SmallNormalFormAddEquiv
import Surreal.Foundations.SmallNormalFormMultiplication

/-!
# The ordered field normal-form equivalence

The proved addition and multiplication laws package canonical evaluation
and extraction as an ordered ring equivalence between the small formal Hahn
field and the actual sign field. Inverses, quotients, powers, and rational
casts then follow from the native field-homomorphism API, including zero
inputs under the fields' totalized inversion operations.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

private theorem single_zero_one_eq_one :
    single (0 : SignSequence.{u}) 1 = (1 : SmallNormalForm.{u}) := by
  apply ext
  intro a
  rw [coeff_single]
  change (if a = 0 then 1 else 0) =
    (1 : _root_.HahnSeries (_root_.Surreal.{u}ᵒᵈ) ℝ).coeff (OrderDual.toDual (toSurreal a))
  simp only [_root_.HahnSeries.coeff_one]
  congr 1
  apply propext
  change a = 0 ↔ toSurreal a = 0
  rw [← toSurreal_zero, toSurreal_inj]

/-- The formal field unit is the singleton real constant one. -/
@[simp] theorem cutEvaluation_one : cutEvaluation (1 : SmallNormalForm.{u}) = 1 := by
  rw [← single_zero_one_eq_one, cutEvaluation_single_zero, map_one]

/-- Canonical evaluation preserves the formal Hahn field's ring operations. -/
def cutEvaluationRingHom : SmallNormalForm.{u} →+* SignSequence.{u} where
  toFun := cutEvaluation
  map_zero' := cutEvaluation_zero
  map_one' := cutEvaluation_one
  map_add' := cutEvaluation_add
  map_mul' := cutEvaluation_mul

@[simp] theorem cutEvaluationRingHom_apply (F : SmallNormalForm.{u}) :
    cutEvaluationRingHom F = cutEvaluation F := rfl

/-- Canonical evaluation and extraction are mutually inverse ring homomorphisms. -/
def cutEvaluationRingEquiv : SmallNormalForm.{u} ≃+* SignSequence.{u} where
  toEquiv := cutEvaluationOrderIso.toEquiv
  map_add' := cutEvaluation_add
  map_mul' := cutEvaluation_mul

@[simp] theorem cutEvaluationRingEquiv_apply (F : SmallNormalForm.{u}) :
    cutEvaluationRingEquiv F = cutEvaluation F := rfl

@[simp] theorem cutEvaluationRingEquiv_symm_apply (x : SignSequence.{u}) :
    cutEvaluationRingEquiv.symm x = normalForm x := rfl

/-- The small formal Hahn field and actual sign field are isomorphic as ordered fields. -/
def cutEvaluationOrderRingIso : SmallNormalForm.{u} ≃+*o SignSequence.{u} where
  toRingEquiv := cutEvaluationRingEquiv
  map_le_map_iff' := cutEvaluation_le_iff _ _

@[simp] theorem cutEvaluationOrderRingIso_apply (F : SmallNormalForm.{u}) :
    cutEvaluationOrderRingIso F = cutEvaluation F := rfl

@[simp] theorem cutEvaluationOrderRingIso_symm_apply (x : SignSequence.{u}) :
    cutEvaluationOrderRingIso.symm x = normalForm x := rfl

@[simp] theorem cutEvaluation_inv (F : SmallNormalForm.{u}) :
    cutEvaluation F⁻¹ = (cutEvaluation F)⁻¹ := map_inv₀ cutEvaluationRingHom F

@[simp] theorem cutEvaluation_div (F G : SmallNormalForm.{u}) :
    cutEvaluation (F / G) = cutEvaluation F / cutEvaluation G :=
  map_div₀ cutEvaluationRingHom F G

@[simp] theorem cutEvaluation_pow (F : SmallNormalForm.{u}) (n : ℕ) :
    cutEvaluation (F ^ n) = cutEvaluation F ^ n := map_pow cutEvaluationRingHom F n

@[simp] theorem cutEvaluation_zpow (F : SmallNormalForm.{u}) (n : ℤ) :
    cutEvaluation (F ^ n) = cutEvaluation F ^ n := map_zpow₀ cutEvaluationRingHom F n

@[simp] theorem cutEvaluation_ratCast (q : ℚ) :
    cutEvaluation (q : SmallNormalForm.{u}) = (q : SignSequence.{u}) :=
  map_ratCast cutEvaluationRingHom q

@[simp] theorem normalForm_one : normalForm (1 : SignSequence.{u}) = 1 :=
  map_one cutEvaluationRingEquiv.symm

@[simp] theorem normalForm_mul (x y : SignSequence.{u}) :
    normalForm (x * y) = normalForm x * normalForm y :=
  map_mul cutEvaluationRingEquiv.symm x y

@[simp] theorem normalForm_inv (x : SignSequence.{u}) :
    normalForm x⁻¹ = (normalForm x)⁻¹ := map_inv₀ cutEvaluationRingEquiv.symm x

@[simp] theorem normalForm_div (x y : SignSequence.{u}) :
    normalForm (x / y) = normalForm x / normalForm y :=
  map_div₀ cutEvaluationRingEquiv.symm x y

@[simp] theorem normalForm_pow (x : SignSequence.{u}) (n : ℕ) :
    normalForm (x ^ n) = normalForm x ^ n := map_pow cutEvaluationRingEquiv.symm x n

@[simp] theorem normalForm_zpow (x : SignSequence.{u}) (n : ℤ) :
    normalForm (x ^ n) = normalForm x ^ n := map_zpow₀ cutEvaluationRingEquiv.symm x n

@[simp] theorem normalForm_ratCast (q : ℚ) :
    normalForm (q : SignSequence.{u}) = (q : SmallNormalForm.{u}) :=
  map_ratCast cutEvaluationRingEquiv.symm q

end

end Surreal.Foundations.SmallNormalForm
