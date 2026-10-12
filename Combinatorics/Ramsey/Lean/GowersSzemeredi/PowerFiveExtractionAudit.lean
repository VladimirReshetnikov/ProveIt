import GowersSzemeredi.IntegerSparseSquareAudit
import Lean.Util.CollectAxioms

/-! A stronger proof-supported Theorem 10.13 density, without changing
any preceding hypothesis or spectrum and Bohr parameter. -/

example : LeanProofs.GowersSzemeredi.theorem_10_13_power_five :=
  LeanProofs.GowersSzemeredi.theorem_10_13_power_five_holds
example : LeanProofs.GowersSzemeredi.theorem_10_13 :=
  LeanProofs.GowersSzemeredi.theorem_10_13_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.theorem_10_13_power_five_holds,
    ``LeanProofs.GowersSzemeredi.theorem_10_13_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the strengthened five-power extraction and its original corrected consequence; only approved axioms."
