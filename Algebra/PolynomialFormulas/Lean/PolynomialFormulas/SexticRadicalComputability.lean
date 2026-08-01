import PolynomialFormulas.QuinticRadicalComputability
import PolynomialFormulas.SexticRadicalDecidability

/-!
# Computability target for integer sextics

This module fixes the exact semantic predicate and the natural-number/Turing
machine interface.  The eventual resolvent decision only has to provide a
primitive-recursive Boolean and its correctness theorem.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.SexticRadicalComputability

open LeanProofs.PolynomialFormulas
open SexticRadicalDecidability

abbrev Coefficients := SexticRadicalDecidability.Coefficients

/-- The target predicate: the tuple has exact degree six and every complex root
of its rational polynomial lies in the radical closure of `ℚ`. -/
def AllRootsRadical (a : Coefficients) : Prop :=
  a.IsSextic ∧ CompletelySolvableByRadicals a.ratPolynomial

@[reducible] private def coefficientEncoding : Encodable Coefficients :=
  (inferInstance : Primcodable Coefficients).toEncodable

@[reducible] private def optionBoolEncoding : Encodable (Option Bool) :=
  (inferInstance : Primcodable (Option Bool)).toEncodable

def coefficientCode (a : Coefficients) : ℕ :=
  @Encodable.encode Coefficients coefficientEncoding a

def criterionResultCode (b : Bool) : ℕ :=
  @Encodable.encode (Option Bool) optionBoolEncoding (some b)

/-- Total natural-number realization of a Boolean sextic criterion. -/
def encodedCriterion (criterion : Coefficients → Bool) (n : ℕ) : ℕ :=
  @Encodable.encode (Option Bool) optionBoolEncoding
    ((@Encodable.decode Coefficients coefficientEncoding n).map criterion)

theorem encodedCriterion_primrec
    (criterion : Coefficients → Bool) (hprim : Primrec criterion) :
    Nat.Primrec (encodedCriterion criterion) := by
  unfold encodedCriterion
  unfold Primrec at hprim
  exact hprim

/-- General-recursive criteria also transfer to their natural-number
realizations.  This is the form used by the sextic search, whose terminating
unbounded minimization is computable but is not claimed primitive recursive. -/
theorem encodedCriterion_computable
    (criterion : Coefficients → Bool) (hcomp : Computable criterion) :
    Computable (encodedCriterion criterion) := by
  unfold encodedCriterion coefficientEncoding optionBoolEncoding
  exact Computable.encode.comp
    (Computable.option_map Computable.decode
      (hcomp.comp Computable.snd))

@[simp] theorem encodedCriterion_coefficientCode
    (criterion : Coefficients → Bool) (a : Coefficients) :
    encodedCriterion criterion (coefficientCode a) =
      criterionResultCode (criterion a) := by
  simp [encodedCriterion, coefficientCode, criterionResultCode]

/-- A primitive-recursive correct Boolean is an actual computable predicate,
not merely a classical `DecidablePred`. -/
theorem computablePred_of_primrec_criterion
    (criterion : Coefficients → Bool)
    (hprim : Primrec criterion)
    (hcorrect : ∀ a, criterion a = true ↔ AllRootsRadical a) :
    ComputablePred AllRootsRadical := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨criterion, hprim.to_comp, ?_⟩
  funext a
  exact propext (hcorrect a).symm

theorem computablePred_of_computable_criterion
    (criterion : Coefficients → Bool)
    (hcomp : Computable criterion)
    (hcorrect : ∀ a, criterion a = true ↔ AllRootsRadical a) :
    ComputablePred AllRootsRadical := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨criterion, hcomp, ?_⟩
  funext a
  exact propext (hcorrect a).symm

/-! ## Concrete machine endpoint -/

def TuringComputesCriterion
    (c : Turing.ToPartrec.Code) (criterion : Coefficients → Bool) : Prop :=
  ∀ a,
    StateTransition.eval
        (Turing.TM2.step Turing.PartrecToTM2.tr)
        (Turing.PartrecToTM2.init c [coefficientCode a]) =
      Part.some (Turing.PartrecToTM2.halt [criterionResultCode (criterion a)])

theorem has_turing_machine_of_primrec_criterion
    (criterion : Coefficients → Bool) (hprim : Primrec criterion) :
    ∃ c : Turing.ToPartrec.Code, TuringComputesCriterion c criterion := by
  obtain ⟨c, hc⟩ :=
    QuinticRadicalComputability.has_turing_machine
      (Primrec.nat_iff.mpr (encodedCriterion_primrec criterion hprim)).to_comp
  refine ⟨c, fun a ↦ ?_⟩
  rw [hc, encodedCriterion_coefficientCode]

theorem has_turing_machine_of_computable_criterion
    (criterion : Coefficients → Bool) (hcomp : Computable criterion) :
    ∃ c : Turing.ToPartrec.Code, TuringComputesCriterion c criterion := by
  obtain ⟨c, hc⟩ :=
    QuinticRadicalComputability.has_turing_machine
      (encodedCriterion_computable criterion hcomp)
  refine ⟨c, fun a ↦ ?_⟩
  rw [hc, encodedCriterion_coefficientCode]

theorem encodedCriterion_accepts_iff
    (criterion : Coefficients → Bool)
    (hcorrect : ∀ a, criterion a = true ↔ AllRootsRadical a)
    (a : Coefficients) :
    encodedCriterion criterion (coefficientCode a) = criterionResultCode true ↔
      AllRootsRadical a := by
  rw [encodedCriterion_coefficientCode]
  unfold criterionResultCode
  rw [@Encodable.encode_inj (Option Bool) optionBoolEncoding]
  simpa using hcorrect a

theorem has_verified_turing_machine_of_primrec_criterion
    (criterion : Coefficients → Bool)
    (hprim : Primrec criterion)
    (hcorrect : ∀ a, criterion a = true ↔ AllRootsRadical a) :
    ∃ c : Turing.ToPartrec.Code,
      TuringComputesCriterion c criterion ∧
      ∀ a,
        encodedCriterion criterion (coefficientCode a) = criterionResultCode true ↔
          AllRootsRadical a := by
  obtain ⟨c, hc⟩ := has_turing_machine_of_primrec_criterion criterion hprim
  exact ⟨c, hc, fun a ↦ encodedCriterion_accepts_iff criterion hcorrect a⟩

theorem has_verified_turing_machine_of_computable_criterion
    (criterion : Coefficients → Bool)
    (hcomp : Computable criterion)
    (hcorrect : ∀ a, criterion a = true ↔ AllRootsRadical a) :
    ∃ c : Turing.ToPartrec.Code,
      TuringComputesCriterion c criterion ∧
      ∀ a,
        encodedCriterion criterion (coefficientCode a) = criterionResultCode true ↔
          AllRootsRadical a := by
  obtain ⟨c, hc⟩ := has_turing_machine_of_computable_criterion criterion hcomp
  exact ⟨c, hc, fun a ↦ encodedCriterion_accepts_iff criterion hcorrect a⟩

end LeanProofs.PolynomialFormulas.SexticRadicalComputability
