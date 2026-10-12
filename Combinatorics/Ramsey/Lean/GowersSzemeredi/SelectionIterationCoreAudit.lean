import GowersSzemeredi.SelectionThresholdCoreAudit
import GowersSzemeredi.Proofs15ThresholdAllPrimes
import GowersSzemeredi.Proofs16PositiveIteration
import GowersSzemeredi.Proofs16Union

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.selection_printed_threshold_three_le,
      ``LeanProofs.GowersSzemeredi.lemma_15_5_printed_threshold_all_primes,
      ``LeanProofs.GowersSzemeredi.IsMultilinear.multiplyLinearFunction_diagonal,
      ``LeanProofs.GowersSzemeredi.lemma_16_8_positive_iteration_counterexample,
      ``LeanProofs.GowersSzemeredi.lemma_16_8_holds] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked selection at every prime, the positive-real iteration counterexample, and the corrected union lemma; only approved axioms."
