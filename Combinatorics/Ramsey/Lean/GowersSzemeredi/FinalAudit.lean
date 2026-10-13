import GowersSzemeredi.Final
import Lean.Util.CollectAxioms

/-! Check the minimal final entry point independently of the legacy aggregate
and the later strengthened bounds. -/

open LeanProofs.GowersSzemeredi in
example : theorem_18_2 := theorem_18_2_explicit

open LeanProofs.GowersSzemeredi in
example : corollary_18_7 := corollary_18_7_explicit

open LeanProofs.GowersSzemeredi in
example : theorem_1_2 := theorem_1_2_explicit

open LeanProofs.GowersSzemeredi in
example : theorem_1_3 := theorem_1_3_explicit

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.theorem_18_2_of_long_progressions,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_padded,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_explicit,
      ``LeanProofs.GowersSzemeredi.corollary_18_7_explicit,
      ``LeanProofs.GowersSzemeredi.theorem_1_2_explicit,
      ``LeanProofs.GowersSzemeredi.theorem_1_3_explicit] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the progression-prefix proof and the original final statements with only approved axioms."
