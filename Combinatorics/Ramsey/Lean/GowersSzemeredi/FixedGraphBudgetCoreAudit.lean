import GowersSzemeredi.Proofs13InitialProgression
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.lemma_13_4_at_real_graph_bound,
      ``LeanProofs.GowersSzemeredi.lemma_13_4_fixed_real_bound,
      ``LeanProofs.GowersSzemeredi.lemma_13_4_holds] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked Lemma 13.4 with the fixed printed real graph budget inside its floor, all larger real budgets, and the existing actual-count version; only approved axioms."
