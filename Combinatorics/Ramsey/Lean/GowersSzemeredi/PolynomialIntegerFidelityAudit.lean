import GowersSzemeredi.IntegerSquareFidelityAudit
import GowersSzemeredi.Proofs16IntegerExplicitRecurrence
import Lean.Util.CollectAxioms

/-! Genuine integer geometry for the polynomial simultaneous recurrence.
This supplies the same explicit profiles used by the structural induction;
the remaining cover constructions must still preserve these certificates. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.ascending_simultaneous_multiaffine_box_height_step,
    ``LeanProofs.GowersSzemeredi.ascendingSimultaneousMultiaffinePartitionBound_zero,
    ``LeanProofs.GowersSzemeredi.AscendingSimultaneousMultiaffinePartitionBound.step,
    ``LeanProofs.GowersSzemeredi.exists_ascending_simultaneous_multiaffine_partition_bound,
    ``LeanProofs.GowersSzemeredi.ascendingMultilinearPartitionBoundAt_of,
    ``LeanProofs.GowersSzemeredi.exists_ascending_simultaneous_multilinear_partition_bound,
    ``LeanProofs.GowersSzemeredi.ascendingCommonDiffPartitionBoundAt_of,
    ``LeanProofs.GowersSzemeredi.exists_ascending_simultaneous_commonDiff_partition_bound,
    ``LeanProofs.GowersSzemeredi.ascendingCommonDiffPartitionTwoBoundAt_of,
    ``LeanProofs.GowersSzemeredi.exists_ascending_simultaneous_commonDiff_partition_two_bound,
    ``LeanProofs.GowersSzemeredi.ascendingPolynomialSection16RecurrenceProfileAt_of,
    ``LeanProofs.GowersSzemeredi.exists_ascending_polynomial_section16_recurrence_profile,
    ``LeanProofs.GowersSzemeredi.ascending_simultaneous_multiaffine_partition_bound_explicit,
    ``LeanProofs.GowersSzemeredi.ascendingMultilinearPartitionBoundAt_explicit,
    ``LeanProofs.GowersSzemeredi.ascendingSection16RecurrenceProfileWith_of_polynomial,
    ``LeanProofs.GowersSzemeredi.AscendingSection16RecurrenceProfileWith.to_integer,
    ``LeanProofs.GowersSzemeredi.ascendingSection16RecurrenceProfileWith_explicit,
    ``LeanProofs.GowersSzemeredi.integerSection16RecurrenceProfileWith_explicit
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked eighteen polynomial integer-partition and recurrence results; only approved axioms."

-- Exact explicit constants used by the existing structural induction.
example : ∀ k : Nat,
    LeanProofs.GowersSzemeredi.IntegerSection16RecurrenceProfileWith k
      (LeanProofs.GowersSzemeredi.familyRecThr k
        (Nat.ceil (LeanProofs.GowersSzemeredi.multiaffinePartitionK (k + 1) (2 ^ (k + 1))))
        ((k + 1) * LeanProofs.GowersSzemeredi.multiaffinePartitionP (k + 1) (2 ^ (k + 1))))
      (LeanProofs.GowersSzemeredi.familyRecExp k
        ((k + 1) * LeanProofs.GowersSzemeredi.multiaffinePartitionP (k + 1) (2 ^ (k + 1)))) :=
  LeanProofs.GowersSzemeredi.integerSection16RecurrenceProfileWith_explicit
