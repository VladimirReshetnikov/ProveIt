import GowersSzemeredi.BaseIntegerFidelityAudit
import GowersSzemeredi.Proofs16IntegerFamilyRemainder
import Lean.Util.CollectAxioms

/-! Genuine abstract family Lemma 16.9 and canonical factor certificates.
The structural induction must still supply its spectrum and remainder covers. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.Box.IsAscendingInteger.axis_hasIntegerRepresentatives,
    ``LeanProofs.GowersSzemeredi.integerAbstractFamilyLemma169At_of,
    ``LeanProofs.GowersSzemeredi.integerAbstractFamilyLemma169At_explicit
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked three genuine family remainder and factor results; only approved axioms."

example : ∀ k : Nat,
    LeanProofs.GowersSzemeredi.IntegerAbstractFamilyLemma169At k
      (LeanProofs.GowersSzemeredi.section16PowerWidth
        (LeanProofs.GowersSzemeredi.familyWidthPrefactor
          (Nat.ceil (LeanProofs.GowersSzemeredi.multiaffinePartitionK (k + 1) (2 ^ (k + 1)))))
        (LeanProofs.GowersSzemeredi.familyWidthDivisor k
          ((k + 1) * LeanProofs.GowersSzemeredi.multiaffinePartitionP (k + 1) (2 ^ (k + 1))))) :=
  LeanProofs.GowersSzemeredi.integerAbstractFamilyLemma169At_explicit
