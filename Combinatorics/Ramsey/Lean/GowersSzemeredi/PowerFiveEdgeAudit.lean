import GowersSzemeredi.PowerFiveExtractionAudit
import GowersSzemeredi.Proofs13PowerFiveEdgeModels
import Lean.Util.CollectAxioms

/-! Check the stronger actual, strong-height and uniform-spectrum edge
extractions with only the standard axioms. -/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.section13_good_height_bohr_model_power_five,
    ``LeanProofs.GowersSzemeredi.section13_strong_height_bohr_model_power_five,
    ``LeanProofs.GowersSzemeredi.section13_uniform_height_bohr_model_power_five
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the three stronger five-power edge extractions; only approved axioms."
