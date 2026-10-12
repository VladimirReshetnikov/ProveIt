import GowersSzemeredi.ModulusFidelityAudit
import GowersSzemeredi.Proofs16IntegerResiduePartition
import Lean.Util.CollectAxioms

/-! Verify the genuine integer-box residue construction with its original
uniform width guarantee, in addition to the earlier fidelity audits. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.Box.width_eq_of_axis_lengths_eq,
    ``LeanProofs.GowersSzemeredi.Box.carrier_eq_of_axis_carriers_eq,
    ``LeanProofs.GowersSzemeredi.Box.HasIntegerRepresentatives.canonical_axes,
    ``LeanProofs.GowersSzemeredi.NatAP.toModAP_section5Transport,
    ``LeanProofs.GowersSzemeredi.integerAxesBox_residue_partition,
    ``LeanProofs.GowersSzemeredi.Box.integer_residue_partition
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked six genuine integer-box residue-partition theorems; only approved axioms."
