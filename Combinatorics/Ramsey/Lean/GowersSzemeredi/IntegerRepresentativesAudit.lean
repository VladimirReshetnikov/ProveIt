import GowersSzemeredi.CompletionAudit
import GowersSzemeredi.Proofs05IntegerRefinement
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
    ``LeanProofs.GowersSzemeredi.integerRun_has_representatives,
    ``LeanProofs.GowersSzemeredi.integerRun_partition,
    ``LeanProofs.GowersSzemeredi.ModAP.integer_representative_partition,
    ``LeanProofs.GowersSzemeredi.ModAP.centered_integer_representative_partition,
    ``LeanProofs.GowersSzemeredi.ModAP.integer_representative_refinement_large,
    ``LeanProofs.GowersSzemeredi.integer_representative_singleton_partition,
    ``LeanProofs.GowersSzemeredi.ModAP.integer_representative_refinement,
    ``LeanProofs.GowersSzemeredi.lemma_5_12_integer_representatives_holds,
    ``LeanProofs.GowersSzemeredi.integer_representative_partition_refinement,
    ``LeanProofs.GowersSzemeredi.lemma_5_13_integer_representatives_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked twenty-two integer-representative theorems; only approved axioms."
