import Surreal.Foundations.SmallNormalFormUnion
import Surreal.Foundations.SmallNormalFormPartialChain
import Surreal.Foundations.SmallNormalFormMonomials
import Surreal.Foundations.SmallNormalFormNegation
import Mathlib.Order.Zorn

/-!
# Canonical extraction of small formal normal forms

Partial approximations to a fixed actual surreal form a small collection:
their evaluated prefixes are determined by birthdays bounded by the target.
A union of an initial-segment chain preserves every recursive center bound.
Zorn's lemma therefore gives a maximal partial approximation. A nonzero
residual would supply a proper extension, so the maximal value is the target.

Together with the comparison theorem this gives an order isomorphism and
inverse extraction on arbitrary small supports. Preservation of addition,
multiplication, and arbitrary admissible sums is a separate obligation.
-/

universe u v

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- Small unions preserve the full approximation invariant. -/
theorem approximates_chainUnion {I : Type v} [Small.{u} I]
    (F : I → SmallNormalForm.{u})
    (h : ∀ i j, IsInitialSegment (F i) (F j) ∨ IsInitialSegment (F j) (F i))
    (x : SignSequence.{u}) (hx : ∀ i, Approximates (F i) x) :
    Approximates (chainUnion F h) x := by
  intro a ha
  obtain ⟨i, hi⟩ := (mem_support_chainUnion F h a).mp ha
  have hs := isInitialSegment_chainUnion F h i
  change (-a : WithTop SignSequence.{u}) < valuation
    (x - (cutEvaluation (trunc (chainUnion F h) a) + ofReal (coeff (chainUnion F h) a) * omegaPower a))
  rw [← hs.trunc_eq hi, ← hs.coeff_eq hi]
  exact hx i a hi

/-- Every actual surreal is the canonical value of a small formal form. -/
theorem cutEvaluation_surjective : Function.Surjective (cutEvaluation : SmallNormalForm.{u} → _) := by
  intro x
  let P := {F : SmallNormalForm.{u} // Approximates F x}
  let R : P → P → Prop := fun F G => IsInitialSegment F.val G.val
  have hub : ∀ c : Set P, IsChain R c → ∃ G : P, ∀ F ∈ c, R F G := by
    intro c hc
    let f : c → SmallNormalForm.{u} := fun i => i.val.val
    have hcomp : ∀ i j, IsInitialSegment (f i) (f j) ∨ IsInitialSegment (f j) (f i) := by
      intro i j
      by_cases he : i.val = j.val
      · left
        change IsInitialSegment i.val.val j.val.val
        rw [he]
      · exact hc i.property j.property he
    have happ : Approximates (chainUnion f hcomp) x :=
      approximates_chainUnion f hcomp x (fun i => i.val.property)
    refine ⟨⟨chainUnion f hcomp, happ⟩, ?_⟩
    intro F hF
    exact isInitialSegment_chainUnion f hcomp ⟨F, hF⟩
  obtain ⟨F, hmax⟩ := exists_maximal_of_chains_bounded hub
    (fun hFG hGH => IsInitialSegment.trans hFG hGH)
  refine ⟨F.val, ?_⟩
  by_contra he
  have hn : x - cutEvaluation F.val ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
  let G : P := ⟨residualExtension F.val x, F.property.extend hn⟩
  have hFG : R F G := by
    simpa only [F.property.trunc_residualExtension hn] using
      trunc_isInitialSegment (residualExtension F.val x)
        (SignSequence.leadingExponent (x - cutEvaluation F.val))
  have hGF := hmax G hFG
  exact F.property.residualExtension_ne hn (IsInitialSegment.antisymm hGF hFG)

/-- Canonical cut evaluation is a bijection preserving the numerical order.
This is an order isomorphism, with field compatibility still to be proved. -/
def cutEvaluationOrderIso : SmallNormalForm.{u} ≃o SignSequence.{u} :=
  OrderIso.ofSurjective cutEvaluationOrderEmbedding cutEvaluation_surjective

@[simp] theorem cutEvaluationOrderIso_apply (F : SmallNormalForm.{u}) :
    cutEvaluationOrderIso F = cutEvaluation F := rfl

/-- The uniquely extracted small formal form of an actual surreal. -/
def normalForm (x : SignSequence.{u}) : SmallNormalForm.{u} := cutEvaluationOrderIso.symm x

@[simp] theorem cutEvaluation_normalForm (x : SignSequence.{u}) :
    cutEvaluation (normalForm x) = x := cutEvaluationOrderIso.apply_symm_apply x

@[simp] theorem normalForm_cutEvaluation (F : SmallNormalForm.{u}) :
    normalForm (cutEvaluation F) = F := cutEvaluationOrderIso.symm_apply_apply F

@[simp] theorem normalForm_zero : normalForm (0 : SignSequence.{u}) = 0 := by
  apply cutEvaluation_injective
  simp

@[simp] theorem normalForm_neg (x : SignSequence.{u}) : normalForm (-x) = -normalForm x := by
  apply cutEvaluation_injective
  simp

@[simp] theorem normalForm_ofReal (r : ℝ) :
    normalForm (ofReal r : SignSequence.{u}) = single 0 r := by
  apply cutEvaluation_injective
  simp

@[simp] theorem normalForm_omegaPower (a : SignSequence.{u}) :
    normalForm (omegaPower a) = single a 1 := by
  apply cutEvaluation_injective
  simp

end

end Surreal.Foundations.SmallNormalForm
