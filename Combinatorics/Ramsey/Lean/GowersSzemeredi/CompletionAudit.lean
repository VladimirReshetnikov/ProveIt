import GowersSzemeredi.NumberedAudit
import GowersSzemeredi.Proofs18CoverSharperComparisons
import Lean.Util.CollectAxioms

/-! Production verification entry point: all numbered catalogue companions
and the stronger inverse, progression, and two-color bounds. -/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let strengthened : Array Name := #[
    ``LeanProofs.GowersSzemeredi.theorem_18_1_sharper_four_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_sharper_six_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d7_four_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L5_eleven_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_sharper_six_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L5_eleven_le,
    ``LeanProofs.GowersSzemeredi.section18ExponentAt_strictAnti,
    ``LeanProofs.GowersSzemeredi.szemerediThresholdAt_strictMono,
    ``LeanProofs.GowersSzemeredi.twoColorThresholdAt_strictMono
  ]
  for name in strengthened do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the nine improved-bound and comparison theorems; only approved axioms."

-- The refutation is checked separately; it is never counted as a proof
-- of the original printed encoding or hidden among the 120 companions.
open Lean Elab Command in
run_cmd do
  let target := ``LeanProofs.GowersSzemeredi.lemma_16_10_printed_unit_encoding
  let proof := ``LeanProofs.GowersSzemeredi.lemma_16_10_packaged_premises_counterexample
  let info ← getConstInfo proof
  unless info.isTheorem && info.type == mkApp (mkConst ``Not) (mkConst target) do
    throwError "The Lemma 16.10 counterexample does not negate its printed encoding"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in (← collectAxioms proof) do
    unless allowed.contains axiomName do
      throwError "{proof} depends on unapproved axiom {axiomName}"
  logInfo "Separately checked the refutation of the printed Lemma 16.10 encoding."
