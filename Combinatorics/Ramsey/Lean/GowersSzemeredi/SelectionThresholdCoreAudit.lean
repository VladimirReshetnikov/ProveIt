import GowersSzemeredi.Proofs15PrintedThreshold
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.selection_dyadic_margin,
      ``LeanProofs.GowersSzemeredi.selectionSharpExplicitThreshold_le,
      ``LeanProofs.GowersSzemeredi.selection_scale_estimate_sharp_explicit,
      ``LeanProofs.GowersSzemeredi.selection_scale_estimate_zero_sharp_explicit,
      ``LeanProofs.GowersSzemeredi.lemma_15_5_printed_threshold,
      ``LeanProofs.GowersSzemeredi.selection_scale_estimate_explicit,
      ``LeanProofs.GowersSzemeredi.selection_scale_estimate_zero_explicit] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the displayed Lemma 15.5 threshold, eta = 1, height zero, and compatibility with the previous thresholds; only approved axioms."
