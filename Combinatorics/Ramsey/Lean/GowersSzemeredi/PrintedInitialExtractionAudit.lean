import GowersSzemeredi.PowerFiveEdgeAudit
import GowersSzemeredi.Proofs13PrintedInitialExtraction
import Lean.Util.CollectAxioms

/-! The printed initial Section 13 extraction in the explicit small-density
range, constructed through a sharper arrangement count. Larger densities
and the unrestricted square corollary remain separate obligations. -/

example : LeanProofs.GowersSzemeredi.lemma_13_6_printed_small_density :=
  LeanProofs.GowersSzemeredi.lemma_13_6_printed_small_density_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.section13_height_count_le_edge_power_fifteen,
    ``LeanProofs.GowersSzemeredi.section13_strong_height_edge_power_fifteen,
    ``LeanProofs.GowersSzemeredi.section13_strong_height_edge_density_cubic,
    ``LeanProofs.GowersSzemeredi.section13_sharp_small_edge_model,
    ``LeanProofs.GowersSzemeredi.section13_printed_uniform_height_model_small_edge,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_of_short_difference_rules_with_length,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_of_bohr_models_with_length,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_from_initial_stages,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_small_row_scale_with_length,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_improved_length,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_small_density_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the sharp edge count and printed initial extraction in the small-density range; only approved axioms."
