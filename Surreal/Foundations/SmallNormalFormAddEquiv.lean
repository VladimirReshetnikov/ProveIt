import Surreal.Foundations.SmallNormalFormAddition
import Surreal.Foundations.SmallNormalFormExtraction
import Surreal.Foundations.SmallNormalFormRealMonomials
import Mathlib.Algebra.Order.Hom.Monoid

/-!
# The ordered additive normal-form equivalence

The separately proved addition law upgrades canonical evaluation and its
inverse extraction to an ordered additive equivalence. Subtraction and
finite sums follow from the native homomorphism API. Multiplication and
inversion are not assumed by this interface.
-/

universe u v

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- Canonical evaluation as an additive homomorphism on all small supports. -/
def cutEvaluationAddHom : SmallNormalForm.{u} →+ SignSequence.{u} where
  toFun := cutEvaluation
  map_zero' := cutEvaluation_zero
  map_add' := cutEvaluation_add

@[simp] theorem cutEvaluationAddHom_apply (F : SmallNormalForm.{u}) :
    cutEvaluationAddHom F = cutEvaluation F := rfl

/-- Evaluation and extraction are mutually inverse additive homomorphisms. -/
def cutEvaluationAddEquiv : SmallNormalForm.{u} ≃+ SignSequence.{u} where
  toEquiv := cutEvaluationOrderIso.toEquiv
  map_add' := cutEvaluation_add

@[simp] theorem cutEvaluationAddEquiv_apply (F : SmallNormalForm.{u}) :
    cutEvaluationAddEquiv F = cutEvaluation F := rfl

@[simp] theorem cutEvaluationAddEquiv_symm_apply (x : SignSequence.{u}) :
    cutEvaluationAddEquiv.symm x = normalForm x := rfl

/-- The canonical normal-form bridge preserves order and addition. -/
def cutEvaluationOrderAddIso : SmallNormalForm.{u} ≃+o SignSequence.{u} where
  toAddEquiv := cutEvaluationAddEquiv
  map_le_map_iff' := cutEvaluation_le_iff _ _

@[simp] theorem cutEvaluationOrderAddIso_apply (F : SmallNormalForm.{u}) :
    cutEvaluationOrderAddIso F = cutEvaluation F := rfl

@[simp] theorem cutEvaluation_sub (F G : SmallNormalForm.{u}) :
    cutEvaluation (F - G) = cutEvaluation F - cutEvaluation G :=
  cutEvaluationAddHom.map_sub F G

/-- Every finite family evaluates by its ordinary field sum. -/
theorem cutEvaluation_sum {I : Type v} (s : Finset I) (F : I → SmallNormalForm.{u}) :
    cutEvaluation (∑ i ∈ s, F i) = ∑ i ∈ s, cutEvaluation (F i) :=
  map_sum cutEvaluationAddHom F s

@[simp] theorem normalForm_add (x y : SignSequence.{u}) :
    normalForm (x + y) = normalForm x + normalForm y := by
  apply cutEvaluation_injective
  simp

@[simp] theorem normalForm_sub (x y : SignSequence.{u}) :
    normalForm (x - y) = normalForm x - normalForm y := by
  apply cutEvaluation_injective
  simp

/-- Inverse extraction recovers every real coefficient at its growth exponent. -/
@[simp] theorem normalForm_real_mul_omegaPower (a : SignSequence.{u}) (r : ℝ) :
    normalForm (ofReal r * omegaPower a) = single a r := by
  apply cutEvaluation_injective
  simp

end

end Surreal.Foundations.SmallNormalForm
