import GowersSzemeredi.Proofs16IntegerOriginalCorollary
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.SplitUniformClass.integerCover_toPower,
      ``LeanProofs.GowersSzemeredi.PowerUniformClass.integerCover_toSplit,
      ``LeanProofs.GowersSzemeredi.splitUniformClass_all_integer,
      ``LeanProofs.GowersSzemeredi.integerPolyCoverAt_one_uniform_low,
      ``LeanProofs.GowersSzemeredi.integerPolyCoverAt_class68,
      ``LeanProofs.GowersSzemeredi.corollary_16_11_integer_of_polyCover,
      ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_bounds,
      ``LeanProofs.GowersSzemeredi.corollary_16_11_integer_shift_eight,
      ``LeanProofs.GowersSzemeredi.corollary_16_11_printed_integer] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked Corollary 16.11 with its original exponent and stronger k+8 exponent, ascending integer boxes, every prime, and only approved axioms."
