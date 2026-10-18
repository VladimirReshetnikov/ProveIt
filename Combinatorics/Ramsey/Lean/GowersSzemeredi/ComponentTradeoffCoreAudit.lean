import GowersSzemeredi.Proofs10Regular
import GowersSzemeredi.Proofs12SourceScope
import Lean.Util.CollectAxioms
import GowersSzemeredi.Proofs10RegularSide

example : LeanProofs.GowersSzemeredi.lemma_10_5_original_sqrt :=
  LeanProofs.GowersSzemeredi.lemma_10_5_original_sqrt_holds
example : LeanProofs.GowersSzemeredi.lemma_10_5_all_tradeoffs :=
  LeanProofs.GowersSzemeredi.lemma_10_5_all_tradeoffs_holds
example : LeanProofs.GowersSzemeredi.proposition_12_1_nonnegative_alpha :=
  LeanProofs.GowersSzemeredi.proposition_12_1_nonnegative_alpha_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[
      ``LeanProofs.GowersSzemeredi.lemma_10_5_all_tradeoffs_holds,
      ``LeanProofs.GowersSzemeredi.lemma_10_5_original_sqrt_holds,
      ``LeanProofs.GowersSzemeredi.lemma_10_5_holds,
      ``LeanProofs.GowersSzemeredi.proposition_12_1_nonnegative_alpha_holds,
      ``LeanProofs.GowersSzemeredi.proposition_12_1_negative_alpha_counterexample] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked three new positive component/sign results, the downstream fifth-power companion and a separate negative-alpha refutation; only approved axioms."
