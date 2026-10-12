import GowersSzemeredi.IntegerNumberedLemma6CoreAudit
import GowersSzemeredi.Proofs16IntegerNumberedLemma9
import GowersSzemeredi.Proofs17IntegerRadius

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.lemma_16_9_integer_representatives,
      ``LeanProofs.GowersSzemeredi.corollary_17_5_integer_radius,
      ``LeanProofs.GowersSzemeredi.corollary_17_6_integer_radius,
      ``LeanProofs.GowersSzemeredi.corollary_17_6_negative_radius_zero_dimension_false] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the integer-box numbered widths, integer-radius finite-pattern bounds and the negative-radius affine endpoint counterexample with only approved axioms."
