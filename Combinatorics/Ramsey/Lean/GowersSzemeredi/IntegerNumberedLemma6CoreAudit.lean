import GowersSzemeredi.Proofs16IntegerNumberedLemma6
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.family_printed_denominator_dominates,
      ``LeanProofs.GowersSzemeredi.source_width_le_max_polynomial,
      ``LeanProofs.GowersSzemeredi.family_printed_width_le_of_power_width,
      ``LeanProofs.GowersSzemeredi.section16Lemma6QBound_tower_lower,
      ``LeanProofs.GowersSzemeredi.section16Lemma6QBound_floor_profile,
      ``LeanProofs.GowersSzemeredi.lemma_16_6_integer_representatives] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked Lemma 16.6 with the numbered width, ascending integer boxes, the source graph budget, every nonzero modulus, and only approved axioms."
