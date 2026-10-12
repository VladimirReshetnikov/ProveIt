import GowersSzemeredi.IntegerBoxesAudit
import GowersSzemeredi.Proofs18IntegerInverseLowDegrees
import GowersSzemeredi.Proofs13SmallIntegerSquare
import Lean.Util.CollectAxioms

/-! Native verification of the genuine inverse theorem and the
all-prime small-width branch, in addition to the preceding catalogue and
geometry audits. This does not assert completion of all paper fidelity. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.Theorem181IntegerAt.to_sharp,
    ``LeanProofs.GowersSzemeredi.Theorem181IntegerAt.mono,
    ``LeanProofs.GowersSzemeredi.Theorem181IntegerAt.of_function_discrepancy,
    ``LeanProofs.GowersSzemeredi.section18ExponentAt_lt_half_of_inv_le,
    ``LeanProofs.GowersSzemeredi.theorem181IntegerAt_of_polyEnvBound,
    ``LeanProofs.GowersSzemeredi.polyGenMuT_integer_slack,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_integer_d7_four_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_integer_three,
    ``LeanProofs.GowersSzemeredi.linear_function_discrepancy_partition,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_integer_zero,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_integer_one,
    ``LeanProofs.GowersSzemeredi.quadratic_discrepancy_fixed_power_lower,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_integer_two,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_integer_d7,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_integer_at_printed,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_integer_representatives_holds,
    ``LeanProofs.GowersSzemeredi.adjacentIntegerAP_hasIntegerRepresentatives,
    ``LeanProofs.GowersSzemeredi.adjacentIntegerAP_mem,
    ``LeanProofs.GowersSzemeredi.cubic_nonuniformity_large_second_fourier,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_integer_small
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked twenty genuine-inverse and small-width theorems; only approved axioms."
