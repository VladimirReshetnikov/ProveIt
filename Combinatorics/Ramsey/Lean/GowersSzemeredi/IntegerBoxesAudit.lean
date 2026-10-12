import GowersSzemeredi.IntegerRepresentativesAudit
import GowersSzemeredi.Proofs16IntegerBoxes
import GowersSzemeredi.Proofs05IntegerPartitionBounds
import Lean.Util.CollectAxioms

/-! Native checks of the short-interval and integer-box representation
lemmas, in addition to the numbered catalogue and genuine refinements. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.ModAP.hasIntegerRepresentatives_congr,
    ``LeanProofs.GowersSzemeredi.ModAP.hasIntegerRepresentatives_of_val_formula,
    ``LeanProofs.GowersSzemeredi.ModAP.reverse_int_val_formula,
    ``LeanProofs.GowersSzemeredi.ModAP.hasIntegerRepresentatives_of_int_val_formula,
    ``LeanProofs.GowersSzemeredi.ModAP.hasIntegerRepresentatives_of_short_interval,
    ``LeanProofs.GowersSzemeredi.NatAP.integer_representatives_transport,
    ``LeanProofs.GowersSzemeredi.Box.HasIntegerRepresentatives.axis,
    ``LeanProofs.GowersSzemeredi.Box.HasIntegerRepresentatives.isProper,
    ``LeanProofs.GowersSzemeredi.Box.reverse_carrier,
    ``LeanProofs.GowersSzemeredi.Box.reverse_width,
    ``LeanProofs.GowersSzemeredi.Box.hasIntegerRepresentatives_of_reverse,
    ``LeanProofs.GowersSzemeredi.Box.hasIntegerRepresentatives_of_nat_axes,
    ``LeanProofs.GowersSzemeredi.Box.hasIntegerRepresentatives_of_int_val_formula,
    ``LeanProofs.GowersSzemeredi.Box.hasIntegerRepresentatives_of_short_interval,
    ``LeanProofs.GowersSzemeredi.boxIndexModel_hasIntegerRepresentatives,
    ``LeanProofs.GowersSzemeredi.NatAP.toModAP_natTransport,
    ``LeanProofs.GowersSzemeredi.Box.integer_representatives_affine_transport,
    ``LeanProofs.GowersSzemeredi.wrappingOneDimensionalBox_isProper,
    ``LeanProofs.GowersSzemeredi.wrappingOneDimensionalBox_noIntegerRepresentatives,
    ``LeanProofs.GowersSzemeredi.IsPartition.sum_eq,
    ``LeanProofs.GowersSzemeredi.IsPartition.norm_sum_le,
    ``LeanProofs.GowersSzemeredi.IsRefinement.sum_norm_mono,
    ``LeanProofs.GowersSzemeredi.partition_averageCellSize,
    ``LeanProofs.GowersSzemeredi.integer_representative_refinement_average,
    ``LeanProofs.GowersSzemeredi.exists_integer_refinement_power_threshold
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked twenty-five short-interval, integer-box, and refinement-bound theorems; only approved axioms."
