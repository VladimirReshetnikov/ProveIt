import GowersSzemeredi.Proofs17PrintedDegreeCounterexample
import GowersSzemeredi.Proofs17ZeroDensity
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.proposition_17_7_zero_parameter_counterexample,
      ``LeanProofs.GowersSzemeredi.proposition_17_2_printed_degree_counterexample,
      ``LeanProofs.GowersSzemeredi.proposition_17_2_prime_range] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the printed-degree and zero-parameter refutations and corrected prime-range proposition; only approved axioms."
