import GowersSzemeredi.BoxPartitionFidelityAudit
import GowersSzemeredi.Proofs16IntegerLemma1
import Lean.Util.CollectAxioms

/-! Genuine integer-box proofs of Lemma 5.10, Corollary 5.11 and Lemma 16.1,
with exact statement checks and complete transitive axiom checks. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.Box.eq_of_axis_eq_commonDiff_eq,
    ``LeanProofs.GowersSzemeredi.Box.IsAscendingInteger.toGenuine,
    ``LeanProofs.GowersSzemeredi.Box.IsAscendingInteger.isProper,
    ``LeanProofs.GowersSzemeredi.boxIndexModel_isAscendingInteger,
    ``LeanProofs.GowersSzemeredi.boxAffineTransport_isAscendingInteger,
    ``LeanProofs.GowersSzemeredi.integerAxesBox_ascending_residue_partition,
    ``LeanProofs.GowersSzemeredi.Box.ascending_residue_partition,
    ``LeanProofs.GowersSzemeredi.multiaffine_integer_box_height_step,
    ``LeanProofs.GowersSzemeredi.ascendingMultilinearHeightAt_holds,
    ``LeanProofs.GowersSzemeredi.ascending_multilinear_partition,
    ``LeanProofs.GowersSzemeredi.genuine_multilinear_partition,
    ``LeanProofs.GowersSzemeredi.lemma_5_10_integer_representatives_holds,
    ``LeanProofs.GowersSzemeredi.ascending_multilinear_simultaneous,
    ``LeanProofs.GowersSzemeredi.genuine_multilinear_simultaneous,
    ``LeanProofs.GowersSzemeredi.corollary_5_11_integer_representatives_holds,
    ``LeanProofs.GowersSzemeredi.boxCons_axis_isAscendingInteger,
    ``LeanProofs.GowersSzemeredi.boxTail_isAscendingInteger,
    ``LeanProofs.GowersSzemeredi.ascending_lemma_16_1,
    ``LeanProofs.GowersSzemeredi.genuine_lemma_16_1,
    ``LeanProofs.GowersSzemeredi.lemma_16_1_integer_representatives_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  let exactStatements : Array (Name × Name) := #[
    (``LeanProofs.GowersSzemeredi.lemma_5_10_integer_representatives,
      ``LeanProofs.GowersSzemeredi.lemma_5_10_integer_representatives_holds),
    (``LeanProofs.GowersSzemeredi.corollary_5_11_integer_representatives,
      ``LeanProofs.GowersSzemeredi.corollary_5_11_integer_representatives_holds),
    (``LeanProofs.GowersSzemeredi.lemma_16_1_integer_representatives,
      ``LeanProofs.GowersSzemeredi.lemma_16_1_integer_representatives_holds)
  ]
  for (target, proof) in exactStatements do
    let info ← getConstInfo proof
    unless info.type == mkConst target do
      throwError "{proof} does not prove exactly {target}"
  logInfo "Checked twenty integer multilinear results and three exact genuine paper statements; only approved axioms."
