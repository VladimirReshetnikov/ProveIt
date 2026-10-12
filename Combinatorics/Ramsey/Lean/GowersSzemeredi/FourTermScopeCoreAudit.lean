import GowersSzemeredi.Proofs08AllModuli
import GowersSzemeredi.Proofs09Restriction
import Lean.Util.CollectAxioms

example : LeanProofs.GowersSzemeredi.theorem_8_2_all_moduli :=
  LeanProofs.GowersSzemeredi.theorem_8_2_all_moduli_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let positive : Array Name := #[
    ``LeanProofs.GowersSzemeredi.hasModAP_four_of_three_quarters_all_moduli,
    ``LeanProofs.GowersSzemeredi.theorem_8_2_all_moduli_holds
  ]
  let refutations : Array Name := #[
    ``LeanProofs.GowersSzemeredi.lemma9_3_unrestricted_eta_counterexample
  ]
  for name in positive ++ refutations do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the two all-modulus four-term results and the separate unrestricted-eta refutation; only approved axioms."
