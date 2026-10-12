import GowersSzemeredi.Proofs05MissingInterval
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.lemma_5_2_printed_half,
      ``LeanProofs.GowersSzemeredi.lemma_5_2_holds] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the original half-bound in Lemma 5.2 and its quarter-bound consequence; only approved axioms."
