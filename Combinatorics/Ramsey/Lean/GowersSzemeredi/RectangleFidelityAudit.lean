import GowersSzemeredi.MultilinearFidelityAudit
import GowersSzemeredi.Proofs13DenseIntegerRectangle
import Lean.Util.CollectAxioms

/-! Common-step integer refinement and dense rectangle extraction.
These are intermediate results toward the large-width case of Theorem 13.12;
this audit does not claim that case is complete. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.ModAP.integer_partition_with_step,
    ``LeanProofs.GowersSzemeredi.common_integer_orientation,
    ``LeanProofs.GowersSzemeredi.ModAP.integer_refinement_at_multiplier,
    ``LeanProofs.GowersSzemeredi.common_integer_refinement_pair,
    ``LeanProofs.GowersSzemeredi.exists_dense_large_rectangle_cell,
    ``LeanProofs.GowersSzemeredi.square_root_rectangle_capacity,
    ``LeanProofs.GowersSzemeredi.IsPartition.inter_subset,
    ``LeanProofs.GowersSzemeredi.IsPartition.product_left,
    ``LeanProofs.GowersSzemeredi.IsPartition.product_right,
    ``LeanProofs.GowersSzemeredi.product_partition_inter_sum_card,
    ``LeanProofs.GowersSzemeredi.dense_common_step_integer_rectangle
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked eleven common-step integer refinement and dense rectangle results; only approved axioms."
