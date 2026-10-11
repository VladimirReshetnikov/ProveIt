import GowersSzemeredi.CompletionAudit
import GowersSzemeredi.Proofs05IntegerRuns
import Lean.Util.CollectAxioms

/-! Native audit of the integer-representative fidelity follow-up, together
with the previously completed numbered-catalogue and stronger-bound audits.
This entry point does not assert completion of all source-fidelity work. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.NatAP.toModAP_carrier,
    ``LeanProofs.GowersSzemeredi.NatAP.toModAP_hasIntegerRepresentatives,
    ``LeanProofs.GowersSzemeredi.ModAP.HasIntegerRepresentatives.isProper,
    ``LeanProofs.GowersSzemeredi.ModAP.HasIntegerRepresentatives.val_carrier,
    ``LeanProofs.GowersSzemeredi.NatAP.toModAP_hasIntegerRepresentatives_of_bound,
    ``LeanProofs.GowersSzemeredi.wrappingThreeTermAP_carrier,
    ``LeanProofs.GowersSzemeredi.wrappingThreeTermAP_isProper,
    ``LeanProofs.GowersSzemeredi.wrappingThreeTermAP_noIntegerRepresentatives,
    ``LeanProofs.GowersSzemeredi.modAP_isProper_does_not_imply_integerRepresentatives,
    ``LeanProofs.GowersSzemeredi.mem_integerRunIndices,
    ``LeanProofs.GowersSzemeredi.integerRunIndices_between,
    ``LeanProofs.GowersSzemeredi.integerRunIndices_eq_Icc,
    ``LeanProofs.GowersSzemeredi.integerRun_has_representatives
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked thirteen integer-representative theorems; only approved axioms."
