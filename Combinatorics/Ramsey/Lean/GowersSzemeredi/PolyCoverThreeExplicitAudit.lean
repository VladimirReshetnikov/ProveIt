import GowersSzemeredi.Proofs16PolyCoverThreeExplicit
import Lean.Util.CollectAxioms

/-! Check the historical explicit dimension-three bridge independently of the
final theorem routes. Its small dimension arithmetic is normalized before
matching the large recurrence constants. -/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.lemma156ExplicitThreshold_two_le,
      ``LeanProofs.GowersSzemeredi.polyCoverAt_three_of_family_lemma6,
      ``LeanProofs.GowersSzemeredi.three_base_facts,
      ``LeanProofs.GowersSzemeredi.theorem_16_2_three,
      ``LeanProofs.GowersSzemeredi.corollary_16_11_three] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the historical explicit dimension-three statements with only approved axioms."
