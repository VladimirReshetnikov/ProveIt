import GowersSzemeredi.Proofs18CoverExplicit
import GowersSzemeredi.Proofs18CoverFejerAllDegrees
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.section16RecurrenceProfileWith_explicit,
      ``LeanProofs.GowersSzemeredi.explicit_family_constants_le,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_explicit,
      ``LeanProofs.GowersSzemeredi.corollary_18_7_explicit,
      ``LeanProofs.GowersSzemeredi.theorem_1_2_explicit,
      ``LeanProofs.GowersSzemeredi.theorem_1_3_explicit,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_L3,
      ``LeanProofs.GowersSzemeredi.van_der_waerden_L3_all,
      ``LeanProofs.GowersSzemeredi.van_der_waerden_L0_thirteen_le] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the simplified recurrence inputs, original final quantitative theorem and strengthened bounds with only approved axioms."
