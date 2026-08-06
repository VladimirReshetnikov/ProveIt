import PolynomialFormulas.SexticReducibleDecision
import PolynomialFormulas.SexticRadicalSemantics

/-!
# Recursive radical-solvability decision for integer sextics

This file assembles the monic decision with integral monicization.  The final
criterion is total recursive (although not claimed primitive recursive,
because the separating-invariant search uses unbounded minimization).
-/

namespace LeanProofs.PolynomialFormulas.SexticRadicalDecision

open SexticRadicalComputability
open SexticRadicalDecidability
open SexticRadicalSemantics
open SexticReducibleDecision

/-- The total Boolean decision on seven integer coefficients.  Malformed
inputs whose leading coefficient is zero are rejected. -/
noncomputable def sexticRadicalDecision
    (a : SexticRadicalComputability.Coefficients) : Bool :=
  a.isSexticB && monicSexticRadicalDecision (monicize a)

theorem sexticRadicalDecision_computable :
    Computable sexticRadicalDecision := by
  exact (Primrec.and.to_comp.comp
    Coefficients.isSexticB_primrec.to_comp
    (monicSexticRadicalDecision_computable.comp monicize_primrec.to_comp)).of_eq
      fun _ ↦ rfl

/-- The Boolean criterion accepts exactly the genuine integer sextics all of
whose complex roots are solvable by radicals over `ℚ`. -/
theorem sexticRadicalDecision_correct
    (a : SexticRadicalComputability.Coefficients) :
    sexticRadicalDecision a = true ↔ AllRootsRadical a := by
  rw [sexticRadicalDecision, Bool.and_eq_true,
    Coefficients.isSexticB_eq_true, AllRootsRadical]
  constructor
  · rintro ⟨ha, hmonic⟩
    exact ⟨ha, (completelySolvableByRadicals_monicize_iff a ha).mp
      ((monicSexticRadicalDecision_correct (monicize a)).mp hmonic)⟩
  · rintro ⟨ha, hrad⟩
    exact ⟨ha, (monicSexticRadicalDecision_correct (monicize a)).mpr
      ((completelySolvableByRadicals_monicize_iff a ha).mpr hrad)⟩

/-- In Mathlib's recursion-theoretic sense, radical solvability of integer
sextics is a computable predicate. -/
theorem allRootsRadical_computablePred : ComputablePred AllRootsRadical := by
  exact computablePred_of_computable_criterion sexticRadicalDecision
    sexticRadicalDecision_computable sexticRadicalDecision_correct

/-- A concrete partial-recursive/Turing-machine code exists for the same
criterion, and its accepting output is proved equivalent to the semantic
radical-solvability predicate. -/
theorem has_verified_sextic_radical_turing_machine :
    ∃ c : Turing.ToPartrec.Code,
      TuringComputesCriterion c sexticRadicalDecision ∧
      ∀ a,
        encodedCriterion sexticRadicalDecision (coefficientCode a) =
            criterionResultCode true ↔
          AllRootsRadical a :=
  has_verified_turing_machine_of_computable_criterion sexticRadicalDecision
    sexticRadicalDecision_computable sexticRadicalDecision_correct

end LeanProofs.PolynomialFormulas.SexticRadicalDecision
