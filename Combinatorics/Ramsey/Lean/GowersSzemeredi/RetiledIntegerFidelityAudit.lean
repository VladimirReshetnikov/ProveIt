import GowersSzemeredi.PolynomialIntegerFidelityAudit
import GowersSzemeredi.Proofs16IntegerRetiledRecurrence
import Lean.Util.CollectAxioms

/-! Genuine final-axis tiling and retiled family linearity. The remaining
short-parent cover and structural induction must supply the integer parents
and retain these certificates; they are not asserted by this audit. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.NatAP.step_ratio_and_span_of_subset,
    ``LeanProofs.GowersSzemeredi.NatAP.step_lt_of_two_le,
    ``LeanProofs.GowersSzemeredi.NatAP.step_eq_of_mod_step_eq,
    ``LeanProofs.GowersSzemeredi.NatAP.partition_at_contained_step,
    ``LeanProofs.GowersSzemeredi.NatAP.carrier_subset_of_mod_carrier_subset,
    ``LeanProofs.GowersSzemeredi.IsPartition.image_injOn,
    ``LeanProofs.GowersSzemeredi.IsNatAPPartition.toModAP,
    ``LeanProofs.GowersSzemeredi.ascending_box_product_tiling_of_contained_integer_axis,
    ``LeanProofs.GowersSzemeredi.ascending_retiled_product_of_recurrence,
    ``LeanProofs.GowersSzemeredi.ascending_retiled_linearity_family_of_recurrence_scale,
    ``LeanProofs.GowersSzemeredi.IntegerSection16RecurrenceProfileWith.retiled_family
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked eleven integer contained-step, product tiling and retiled family results; only approved axioms."
