import GowersSzemeredi.StructureIntegerFidelityAudit
import GowersSzemeredi.Proofs13PrintedSquareBounds
import Lean.Util.CollectAxioms

/-! Native exact-type and axiom checks for the printed contextual Section 13
bounds. This does not prove the stronger upstream Lemma 13.6 extraction or
the square corollary's ordinary integer-representative interpretation. -/

example : LeanProofs.GowersSzemeredi.lemma_13_7_printed_bounds :=
  LeanProofs.GowersSzemeredi.lemma_13_7_printed_bounds_holds
example : LeanProofs.GowersSzemeredi.lemma_13_8_printed_bounds :=
  LeanProofs.GowersSzemeredi.lemma_13_8_printed_bounds_holds
example : LeanProofs.GowersSzemeredi.lemma_13_9_printed_bounds :=
  LeanProofs.GowersSzemeredi.lemma_13_9_printed_bounds_holds
example : LeanProofs.GowersSzemeredi.corollary_13_10_printed_bounds :=
  LeanProofs.GowersSzemeredi.corollary_13_10_printed_bounds_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.IsStage136DataPrinted.to_encoded,
    ``LeanProofs.GowersSzemeredi.stage137Printed_partition_exponent,
    ``LeanProofs.GowersSzemeredi.stage136Printed_exists_base_row,
    ``LeanProofs.GowersSzemeredi.lemma_13_7_printed_of_empty_heights_with_step_span,
    ``LeanProofs.GowersSzemeredi.lemma_13_7_printed_all_scales_with_step_span,
    ``LeanProofs.GowersSzemeredi.lemma_13_7_printed_bounds_holds,
    ``LeanProofs.GowersSzemeredi.lemma_13_8_printed_with_domain,
    ``LeanProofs.GowersSzemeredi.lemma_13_8_printed_bounds_holds,
    ``LeanProofs.GowersSzemeredi.stage139Printed_partition_exponent,
    ``LeanProofs.GowersSzemeredi.lemma_13_9_printed_with_localized_step_span,
    ``LeanProofs.GowersSzemeredi.lemma_13_9_printed_small_columns,
    ``LeanProofs.GowersSzemeredi.lemma_13_9_printed_all_scales_with_geometry,
    ``LeanProofs.GowersSzemeredi.stage139Printed_support_of_stage137_stage138,
    ``LeanProofs.GowersSzemeredi.lemma_13_9_printed_bounds_holds,
    ``LeanProofs.GowersSzemeredi.corollary_13_10_printed_of_integer_step_fit,
    ``LeanProofs.GowersSzemeredi.corollary_13_10_printed_of_tiny_cell,
    ``LeanProofs.GowersSzemeredi.corollary_13_10_printed_of_construction_geometry,
    ``LeanProofs.GowersSzemeredi.corollary_13_10_printed_bounds_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the printed contextual Section 13 bounds with only approved axioms; upstream extraction and square integer geometry remain separate."
