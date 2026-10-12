import GowersSzemeredi.ComponentTradeoffCoreAudit
import GowersSzemeredi.Proofs13PurifiedContext
import GowersSzemeredi.Proofs13SourceScope
import Lean.Util.CollectAxioms

example : LeanProofs.GowersSzemeredi.lemma_13_11_original_error :=
  LeanProofs.GowersSzemeredi.lemma_13_11_original_error_holds
example : LeanProofs.GowersSzemeredi.lemma_13_11_purified 73 :=
  LeanProofs.GowersSzemeredi.lemma_13_11_purified_seventy_three
example : LeanProofs.GowersSzemeredi.lemma_13_1_nonnegative_alpha :=
  LeanProofs.GowersSzemeredi.lemma_13_1_nonnegative_alpha_holds
example : LeanProofs.GowersSzemeredi.corollary_13_2_nonnegative_alpha :=
  LeanProofs.GowersSzemeredi.corollary_13_2_nonnegative_alpha_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let positive : Array Name := #[
    ``LeanProofs.GowersSzemeredi.lemma_13_11_purified_holds,
    ``LeanProofs.GowersSzemeredi.lemma_13_11_purified_seventy_three,
    ``LeanProofs.GowersSzemeredi.lemma_13_11_original_error_holds,
    ``LeanProofs.GowersSzemeredi.lemma_13_1_nonnegative_alpha_holds,
    ``LeanProofs.GowersSzemeredi.corollary_13_2_nonnegative_alpha_holds
  ]
  let refutations : Array Name := #[
    ``LeanProofs.GowersSzemeredi.lemma_13_1_negative_alpha_counterexample,
    ``LeanProofs.GowersSzemeredi.corollary_13_2_negative_alpha_counterexample,
    ``LeanProofs.GowersSzemeredi.proposition_12_1_negative_alpha_counterexample
  ]
  for name in positive ++ refutations do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked five new purification/sign results and three separate prime-modulus sign refutations; only approved axioms."
