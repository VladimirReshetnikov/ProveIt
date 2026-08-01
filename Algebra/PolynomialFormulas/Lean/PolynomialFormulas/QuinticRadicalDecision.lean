import PolynomialFormulas.QuinticGaloisCriterion
import PolynomialFormulas.QuinticRadicalPrimrec
import PolynomialFormulas.QuinticRadicalSemantics
import PolynomialFormulas.QuinticScalarResolventCriterion

/-!
# Assembling a radical-solvability decision for integer quintics

This module isolates the reusable reducible/irreducible case split.  Any
primitive-recursive Boolean test which recognizes solvability of the Galois
group for irreducible monic quintics extends to a primitive-recursive test for
radical solvability of arbitrary six-coefficient integer inputs.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.QuinticRadicalDecision

open LeanProofs.PolynomialFormulas
open QuinticRadicalComputability
open QuinticRadicalDecidability
open QuinticRadicalSemantics
open QuinticRadicalPrimrec
open QuinticDummitCoefficients
open ComputableDummitCoefficients
open QuinticScalarResolventCriterion

/-- Extend an irreducible-monic criterion to arbitrary coefficient tuples.
Malformed inputs are rejected; reducible monicizations are accepted because
all of their irreducible factors have degree at most four. -/
def decisionWith (irreducibleCriterion : MonicQuintic → Bool)
    (a : Coefficients) : Bool :=
  IntegerQuintic.isQuinticB a &&
    (MonicQuintic.hasBoundedProperFactor (monicize a) ||
      irreducibleCriterion (monicize a))

theorem decisionWith_primrec (irreducibleCriterion : MonicQuintic → Bool)
    (hcriterion : Primrec irreducibleCriterion) :
    Primrec (decisionWith irreducibleCriterion) := by
  exact Primrec.and.comp IntegerQuintic.isQuinticB_primrec
    (Primrec.or.comp
      (hasBoundedProperFactor_primrec.comp monicize_primrec)
      (hcriterion.comp monicize_primrec))

/-- Correctness of the complete decision follows from correctness of its
irreducible-monic branch. -/
theorem decisionWith_correct (irreducibleCriterion : MonicQuintic → Bool)
    (hcriterion : ∀ f : MonicQuintic,
      Irreducible (f.polynomial.map (Int.castRingHom ℚ)) →
        (irreducibleCriterion f = true ↔
          IsSolvable (f.polynomial.map (Int.castRingHom ℚ)).Gal))
    (a : Coefficients) :
    decisionWith irreducibleCriterion a = true ↔ AllRootsRadical a := by
  constructor
  · intro h
    rw [decisionWith, Bool.and_eq_true, Bool.or_eq_true,
      IntegerQuintic.isQuinticB_eq_true] at h
    rcases h with ⟨ha, hred | hcriterionTrue⟩
    · apply allRootsRadical_of_monicize_not_irreducible a ha
      exact
        (hasBoundedProperFactor_iff_monicRatPolynomial_not_irreducible a).mp hred
    · by_cases hirr : Irreducible (monicRatPolynomial a)
      · refine ⟨ha, (completelySolvableByRadicals_monicize_iff a ha).mp ?_⟩
        exact (completelySolvableByRadicals_iff_gal_isSolvable_of_irreducible
          hirr (monicRatPolynomial_natDegree a)).mpr
            ((hcriterion (monicize a)
              (by simpa [monicRatPolynomial] using hirr)).mp hcriterionTrue)
      · exact allRootsRadical_of_monicize_not_irreducible a ha hirr
  · rintro ⟨ha, hrad⟩
    rw [decisionWith, Bool.and_eq_true, Bool.or_eq_true,
      IntegerQuintic.isQuinticB_eq_true]
    refine ⟨ha, ?_⟩
    by_cases hirr : Irreducible (monicRatPolynomial a)
    · right
      apply (hcriterion (monicize a)
        (by simpa [monicRatPolynomial] using hirr)).mpr
      apply (completelySolvableByRadicals_iff_gal_isSolvable_of_irreducible
        hirr (monicRatPolynomial_natDegree a)).mp
      exact (completelySolvableByRadicals_monicize_iff a ha).mpr hrad
    · left
      exact
        (hasBoundedProperFactor_iff_monicRatPolynomial_not_irreducible a).mpr hirr

/-! ## The concrete Frobenius--Dummit decision -/

/-- Executable bounded rational-root search on the certified sparse-table
Frobenius--Dummit sextic. -/
def dummitCriterion (f : MonicQuintic) : Bool :=
  (explicitDummitCoefficients f).rationalRootSearch

theorem dummitCriterion_primrec : Primrec dummitCriterion := by
  exact IntegerSextic.rationalRootSearch_primrec.comp
    explicitDummitCoefficients_primrec

/-- On an irreducible monic quintic, the concrete coefficient criterion is
equivalent to solvability of the Galois group. -/
theorem dummitCriterion_correct (f : MonicQuintic)
    (hp : Irreducible (f.polynomial.map (Int.castRingHom ℚ))) :
    dummitCriterion f = true ↔
      IsSolvable (f.polynomial.map (Int.castRingHom ℚ)).Gal := by
  change (explicitDummitCoefficients f).rationalRootSearch = true ↔
    IsSolvable (monicQuinticRatPolynomial f).Gal
  exact explicitDummitRationalRootSearch_iff_gal_isSolvable f
    (by simpa [monicQuinticRatPolynomial] using hp)

/-- The directly evaluable Boolean decision on six integer coefficients. -/
def quinticRadicalDecision : Coefficients → Bool :=
  decisionWith dummitCriterion

theorem quinticRadicalDecision_primrec : Primrec quinticRadicalDecision :=
  decisionWith_primrec dummitCriterion dummitCriterion_primrec

/-- The coefficient decision accepts exactly the genuine integer quintics all
of whose complex roots are expressible by radicals over `ℚ`. -/
theorem quinticRadicalDecision_correct (a : Coefficients) :
    quinticRadicalDecision a = true ↔ AllRootsRadical a :=
  decisionWith_correct dummitCriterion dummitCriterion_correct a

/-- Radical solvability of integer quintics is a computable predicate. -/
theorem allRootsRadical_computablePred : ComputablePred AllRootsRadical :=
  computablePred_of_primrec_criterion quinticRadicalDecision
    quinticRadicalDecision_primrec quinticRadicalDecision_correct

/-- A `PartrecToTM2` program exists which realizes the verified coefficient
decision on the canonical natural-number encoding. -/
theorem has_verified_quinticRadicalDecision_turingMachine :
    ∃ c : Turing.ToPartrec.Code,
      TuringComputesCriterion c quinticRadicalDecision ∧
      ∀ a,
        encodedCriterion quinticRadicalDecision (coefficientCode a) =
            criterionResultCode true ↔
          AllRootsRadical a :=
  has_verified_turing_machine_of_primrec_criterion quinticRadicalDecision
    quinticRadicalDecision_primrec quinticRadicalDecision_correct

end LeanProofs.PolynomialFormulas.QuinticRadicalDecision
