import Surreal.Foundations.SmallNormalFormAddEquiv
import Surreal.Foundations.SignSequenceMonomialAlgebra

/-!
# Agreement with finite monomial evaluation

Finite families of singleton formal forms evaluate to the corresponding
actual sums of real monomials. A finitely supported monoid-algebra expression
therefore has the same value under the small normal-form bridge and under
the existing finite monomial evaluation. Increasing `t` exponents become
negative Conway growth exponents; repeated exponents and cancellation are
handled by the finite sums themselves.
-/

universe u v w

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- Every finite sum of formal real monomials evaluates by the actual field sum.
No distinctness or ordering of the exponents is required. -/
theorem cutEvaluation_sum_single {I : Type v} (s : Finset I)
    (a : I → SignSequence.{u}) (r : I → ℝ) :
    cutEvaluation (∑ i ∈ s, single (a i) (r i)) =
      ∑ i ∈ s, ofReal (r i) * omegaPower (a i) := by
  rw [cutEvaluation_sum]
  simp only [cutEvaluation_single]

variable {Γ : Type v} [AddMonoid Γ]

/-- Convert a finite monoid-algebra expression to a small formal normal form.
The exponent map need not be injective or preserve any chosen order. -/
def ofFiniteMonomialForm (e : Γ →+ SignSequence.{u})
    (F : AddMonoidAlgebra ℝ Γ) : SmallNormalForm.{u} :=
  F.coeff.sum (fun γ r => single (-(e γ)) r)

/-- The two independently constructed evaluation maps agree on every finite form. -/
@[simp] theorem cutEvaluation_ofFiniteMonomialForm (e : Γ →+ SignSequence.{u})
    (F : AddMonoidAlgebra ℝ Γ) :
    cutEvaluation (ofFiniteMonomialForm e F) = finiteMonomialEvaluation e F := by
  rw [finiteMonomialEvaluation_eq_sum]
  change cutEvaluation (∑ γ ∈ F.coeff.support, single (-(e γ)) (F.coeff γ)) = _
  rw [cutEvaluation_sum_single]
  rfl

/-- Extraction of an actual finite monomial sum recovers its finite formal conversion. -/
@[simp] theorem normalForm_finiteMonomialEvaluation (e : Γ →+ SignSequence.{u})
    (F : AddMonoidAlgebra ℝ Γ) :
    normalForm (finiteMonomialEvaluation e F) = ofFiniteMonomialForm e F := by
  apply cutEvaluation_injective
  simp

@[simp] theorem ofFiniteMonomialForm_zero (e : Γ →+ SignSequence.{u}) :
    ofFiniteMonomialForm e 0 = 0 := by
  apply cutEvaluation_injective
  simp

/-- A finite singleton changes from the increasing `t` convention to the
negative growth exponent, with its coefficient unchanged. -/
@[simp] theorem ofFiniteMonomialForm_single (e : Γ →+ SignSequence.{u})
    (γ : Γ) (r : ℝ) :
    ofFiniteMonomialForm e (AddMonoidAlgebra.single γ r) = single (-(e γ)) r := by
  apply cutEvaluation_injective
  simp only [cutEvaluation_ofFiniteMonomialForm, finiteMonomialEvaluation_single,
    cutEvaluation_single, tMonomial]

end

end Surreal.Foundations.SmallNormalForm
