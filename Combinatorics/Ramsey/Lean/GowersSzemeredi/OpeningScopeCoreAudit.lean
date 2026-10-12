import GowersSzemeredi.Proofs01HeadlineScale
import GowersSzemeredi.Proofs02RoundingCounterexample
import Lean.Util.CollectAxioms

/-! Check two literal finite/rounding refutations separately from the
positive corrected companions. -/

example : ¬ LeanProofs.GowersSzemeredi.theorem_1_3_without_eventual_scale :=
  LeanProofs.GowersSzemeredi.theorem_1_3_without_eventual_scale_counterexample
example : ¬ LeanProofs.GowersSzemeredi.lemma_2_3_without_rounding_correction :=
  LeanProofs.GowersSzemeredi.lemma_2_3_without_rounding_correction_counterexample

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.no_natAP_longer_than_interval,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_without_eventual_scale_counterexample,
    ``LeanProofs.GowersSzemeredi.lemma_2_3_without_rounding_correction_counterexample
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked interval obstruction and two separate literal-form refutations; only approved axioms."
