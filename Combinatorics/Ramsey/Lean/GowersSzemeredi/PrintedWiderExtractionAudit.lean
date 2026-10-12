import GowersSzemeredi.PrintedInitialExtractionAudit
import GowersSzemeredi.Proofs13PrintedWiderExtraction
import Lean.Util.CollectAxioms

example : LeanProofs.GowersSzemeredi.lemma_13_6_printed_wider_density :=
  LeanProofs.GowersSzemeredi.lemma_13_6_printed_wider_density_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
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
  logInfo "Checked the original printed extraction up to density14/15; only approved axioms."
