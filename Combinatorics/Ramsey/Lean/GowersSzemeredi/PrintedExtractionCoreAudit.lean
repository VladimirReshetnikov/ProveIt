import GowersSzemeredi.Proofs13PowerFiveEdgeModels
import GowersSzemeredi.Proofs13PrintedWiderExtraction
import Lean.Util.CollectAxioms

/-! Direct kernel and axiom checks for the stronger extraction and original
printed Section 13 bounds up to14/15. The full downstream catalogue audit
is a separate gate, and the larger-density interval remains open. -/

example : LeanProofs.GowersSzemeredi.theorem_10_13_power_five :=
  LeanProofs.GowersSzemeredi.theorem_10_13_power_five_holds
example : LeanProofs.GowersSzemeredi.lemma_13_6_printed_wider_density :=
  LeanProofs.GowersSzemeredi.lemma_13_6_printed_wider_density_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.theorem_10_13_power_five_holds,
    ``LeanProofs.GowersSzemeredi.theorem_10_13_holds,
    ``LeanProofs.GowersSzemeredi.section13_good_height_bohr_model_power_five,
    ``LeanProofs.GowersSzemeredi.section13_strong_height_bohr_model_power_five,
    ``LeanProofs.GowersSzemeredi.section13_uniform_height_bohr_model_power_five,
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
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_small_density_holds,
    ``LeanProofs.GowersSzemeredi.section13_printed_uniform_height_model,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_from_initial_stages_wider,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_improved_length_wider,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_wider_density_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked twenty extraction and sharp-count results directly; only approved axioms."
