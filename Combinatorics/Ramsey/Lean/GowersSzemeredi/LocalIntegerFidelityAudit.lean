import GowersSzemeredi.RetiledIntegerFidelityAudit
import GowersSzemeredi.Proofs16IntegerFamilyLemma6
import GowersSzemeredi.Proofs16IntegerLossRange
import Lean.Util.CollectAxioms
import GowersSzemeredi.Proofs16BoxGeometrySide

/-! Genuine short-parent covers and the abstract family Lemma 16.6.
The literal uncapped loss assertion is refuted separately from these proofs. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.NatAP.bounded_partition,
    ``LeanProofs.GowersSzemeredi.Box.ascending_bounded_partition,
    ``LeanProofs.GowersSzemeredi.Box.ascending_short_parent_partition,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.mono,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.on_partition,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.short_parent_cover,
    ``LeanProofs.GowersSzemeredi.boxInit_isAscendingInteger,
    ``LeanProofs.GowersSzemeredi.pointSingletonBox_isAscendingInteger,
    ``LeanProofs.GowersSzemeredi.boxInit_carrier_eq_of_box_carrier_eq,
    ``LeanProofs.GowersSzemeredi.integerAbstractFamilyLemma166At_of,
    ``LeanProofs.GowersSzemeredi.integerAbstractFamilyLemma166At_explicit
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked eleven integer short-parent and family Lemma 16.6 results; only approved axioms."
  let counterexample := ``LeanProofs.GowersSzemeredi.multipleLinearity_uncapped_loss_counterexample
  let info ← getConstInfo counterexample
  unless info.isTheorem do
    throwError "The uncapped loss counterexample is not a theorem"
  for axiomName in (← collectAxioms counterexample) do
    unless allowed.contains axiomName do
      throwError "The uncapped loss counterexample depends on {axiomName}"
  logInfo "Separately checked the existing refutation of the literal uncapped loss quantifier."
  for axiomName in (← collectAxioms
      ``LeanProofs.GowersSzemeredi.multipleLinearity_uncapped_integer_loss_counterexample) do
    unless allowed.contains axiomName do
      throwError "The genuine integer-box uncapped-loss refutation depends on {axiomName}"
  logInfo "Separately checked the uncapped-loss refutation with genuine integer input and output boxes."

example : ∀ k : Nat,
    LeanProofs.GowersSzemeredi.IntegerAbstractFamilyLemma166At k
      (LeanProofs.GowersSzemeredi.section16PowerWidth
        (LeanProofs.GowersSzemeredi.familyWidthPrefactor
          (Nat.ceil (LeanProofs.GowersSzemeredi.multiaffinePartitionK (k + 1) (2 ^ (k + 1)))))
        (LeanProofs.GowersSzemeredi.familyWidthDivisor k
          ((k + 1) * LeanProofs.GowersSzemeredi.multiaffinePartitionP (k + 1) (2 ^ (k + 1))))) :=
  LeanProofs.GowersSzemeredi.integerAbstractFamilyLemma166At_explicit
