import PolynomialFormulas.AbelRuffini
import PolynomialFormulas.QuinticRadicalDecidability
import Mathlib.Computability.RE
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# A conditional computability bridge for integer quintics

An integer polynomial of degree at most five is represented by its six
coefficients.  `AllRootsRadical` restricts this representation to genuine
quintics and gives the intended semantic statement using
`CompletelySolvableByRadicals`.

This module deliberately does **not** construct a decision criterion for that
semantic predicate.  Its main theorems instead make the missing mathematical
step explicit: given a Boolean criterion, a proof that it is primitive
recursive, and a proof that it is correct on every coefficient vector, the
semantic predicate is computable and the criterion is executed by mathlib's
concrete `PartrecToTM2` Turing-machine simulator.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.QuinticRadicalComputability

/-- Coefficients `a 0, ..., a 5` of an integer polynomial of degree at most five. -/
abbrev Coefficients := QuinticRadicalDecidability.IntegerQuintic

/-- The shared integer-polynomial view of the six coefficients. -/
noncomputable def intPolynomial (a : Coefficients) : ℤ[X] :=
  QuinticRadicalDecidability.IntegerQuintic.polynomial a

/-- The same polynomial, with its coefficients mapped to the rationals. -/
noncomputable def ratPolynomial (a : Coefficients) : ℚ[X] :=
  (intPolynomial a).map (Int.castRingHom ℚ)

/-- The target semantic predicate.  The leading-coefficient condition makes
the coefficient vector represent an actual quintic rather than a polynomial
of smaller degree. -/
def AllRootsRadical (a : Coefficients) : Prop :=
  a 5 ≠ 0 ∧ CompletelySolvableByRadicals (ratPolynomial a)

/-!
The public coding functions below use the encoding supplied by the
`Primcodable` instances.  Naming that encoding avoids silently mixing it with
another `Encodable` instance for the same function type.
-/

@[reducible] private def coefficientEncoding : Encodable Coefficients :=
  (inferInstance : Primcodable Coefficients).toEncodable

@[reducible] private def optionBoolEncoding : Encodable (Option Bool) :=
  (inferInstance : Primcodable (Option Bool)).toEncodable

/-- The natural-number code used as input for a coefficient vector. -/
def coefficientCode (a : Coefficients) : ℕ :=
  @Encodable.encode Coefficients coefficientEncoding a

/-- The natural-number output code for a successful Boolean criterion call. -/
def criterionResultCode (b : Bool) : ℕ :=
  @Encodable.encode (Option Bool) optionBoolEncoding (some b)

/-- A total natural-number realization of a coefficient criterion.  Invalid
natural-number inputs are sent to the encoding of `none`; valid coefficient
codes are sent to `criterionResultCode`. -/
def encodedCriterion (criterion : Coefficients → Bool) (n : ℕ) : ℕ :=
  @Encodable.encode (Option Bool) optionBoolEncoding
    ((@Encodable.decode Coefficients coefficientEncoding n).map criterion)

/-- Primitive recursiveness of a coefficient criterion transfers directly to
its total natural-number realization. -/
theorem encodedCriterion_primrec
    (criterion : Coefficients → Bool) (hprim : Primrec criterion) :
    Nat.Primrec (encodedCriterion criterion) := by
  unfold encodedCriterion
  unfold Primrec at hprim
  exact hprim

/-- On a valid coefficient code, `encodedCriterion` returns the code of the
Boolean result. -/
theorem encodedCriterion_coefficientCode
    (criterion : Coefficients → Bool) (a : Coefficients) :
    encodedCriterion criterion (coefficientCode a) =
      criterionResultCode (criterion a) := by
  simp [encodedCriterion, coefficientCode, criterionResultCode]

/-- The exact recursive-decidability conclusion, conditional on an explicit
primitive-recursive criterion and its semantic correctness proof. -/
theorem computablePred_of_primrec_criterion
    (criterion : Coefficients → Bool)
    (hprim : Primrec criterion)
    (hcorrect : ∀ a, criterion a = true ↔ AllRootsRadical a) :
    ComputablePred AllRootsRadical := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨criterion, hprim.to_comp, ?_⟩
  funext a
  exact propext (hcorrect a).symm

/-! ## From recursive functions to concrete machine executions -/

/-- A computable unary natural-number function has a partial-recursive program
code with the expected total behavior. -/
theorem has_partrec_code {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Nat.Partrec.Code, c.eval = fun n => Part.some (f n) := by
  exact Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec)

/-- A computable unary natural-number function has code in the list-machine
basis used by `PartrecToTM2`. -/
theorem has_turing_code {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Turing.ToPartrec.Code,
      ∀ n, c.eval [n] = Part.some [f n] := by
  have hv : Computable (fun v : List.Vector ℕ 1 => f v.head) :=
    hf.comp Primrec.vector_head.to_comp
  obtain ⟨c, hc⟩ :=
    Turing.ToPartrec.Code.exists_code (Nat.Partrec'.of_part hv.partrec)
  refine ⟨c, fun n => ?_⟩
  simpa [List.Vector.head] using hc (⟨[n], by simp⟩ : List.Vector ℕ 1)

/-- The concrete `PartrecToTM2` execution relation for a unary function. -/
def TuringComputes (c : Turing.ToPartrec.Code) (f : ℕ → ℕ) : Prop :=
  ∀ n,
    StateTransition.eval
        (Turing.TM2.step Turing.PartrecToTM2.tr)
        (Turing.PartrecToTM2.init c [n]) =
      Part.some (Turing.PartrecToTM2.halt [f n])

/-- Every computable unary natural-number function is run by a concrete
`PartrecToTM2` program. -/
theorem has_turing_machine {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Turing.ToPartrec.Code, TuringComputes c f := by
  obtain ⟨c, hc⟩ := has_turing_code hf
  refine ⟨c, fun n => ?_⟩
  rw [Turing.PartrecToTM2.tr_eval, hc]
  rfl

/-- The concrete machine behavior expected of a coefficient criterion. -/
def TuringComputesCriterion
    (c : Turing.ToPartrec.Code) (criterion : Coefficients → Bool) : Prop :=
  ∀ a,
    StateTransition.eval
        (Turing.TM2.step Turing.PartrecToTM2.tr)
        (Turing.PartrecToTM2.init c [coefficientCode a]) =
      Part.some (Turing.PartrecToTM2.halt [criterionResultCode (criterion a)])

/-- A primitive-recursive coefficient criterion has a concrete Turing-machine
implementation on coefficient codes.  This theorem concerns execution only;
semantic correctness is a separate hypothesis below. -/
theorem has_turing_machine_of_primrec_criterion
    (criterion : Coefficients → Bool)
    (hprim : Primrec criterion) :
    ∃ c : Turing.ToPartrec.Code, TuringComputesCriterion c criterion := by
  obtain ⟨c, hc⟩ := has_turing_machine
    (Primrec.nat_iff.mpr (encodedCriterion_primrec criterion hprim)).to_comp
  refine ⟨c, fun a => ?_⟩
  rw [hc, encodedCriterion_coefficientCode]

/-- Correctness of the natural-number output code is exactly correctness of
the original Boolean criterion. -/
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

/-- Bundled conditional endpoint: the supplied criterion is executed by a
concrete Turing machine, while the separate correctness clause identifies its
accepting output code with semantic solvability by radicals. -/
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
  refine ⟨c, hc, fun a => ?_⟩
  exact encodedCriterion_accepts_iff criterion hcorrect a

end LeanProofs.PolynomialFormulas.QuinticRadicalComputability
