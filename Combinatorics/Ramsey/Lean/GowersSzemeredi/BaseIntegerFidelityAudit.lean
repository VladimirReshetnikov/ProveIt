import GowersSzemeredi.LocalIntegerFidelityAudit
import GowersSzemeredi.Proofs16IntegerBaseSourceBounds
import Lean.Util.CollectAxioms

/-! Genuine dimension-one relation covers from the global product property,
including the exact printed-parameter statement of Lemma 16.3. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.indexCellBox_isAscendingInteger,
    ``LeanProofs.GowersSzemeredi.section16_integer_coarse_relation_cover,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.of_ascending,
    ``LeanProofs.GowersSzemeredi.section16_ascending_freiman_family_poly_cover,
    ``LeanProofs.GowersSzemeredi.section16_integer_freiman_family_poly_cover,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.weaken,
    ``LeanProofs.GowersSzemeredi.section16_integer_freiman_family_cubic_cover,
    ``LeanProofs.GowersSzemeredi.section16_product_relation_integer_cubic_cover,
    ``LeanProofs.GowersSzemeredi.integerPolyCoverAt_one,
    ``LeanProofs.GowersSzemeredi.section16_integer_base_source_budget,
    ``LeanProofs.GowersSzemeredi.integer_cubic_base_controls_fit,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.base_source_controls,
    ``LeanProofs.GowersSzemeredi.lemma_16_3_integer_representatives_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  let info ← getConstInfo ``LeanProofs.GowersSzemeredi.lemma_16_3_integer_representatives_holds
  unless info.type == mkConst ``LeanProofs.GowersSzemeredi.lemma_16_3_integer_representatives do
    throwError "The genuine Lemma 16.3 companion does not prove its exact statement"
  logInfo "Checked thirteen genuine base-cover results and exact Lemma 16.3; only approved axioms."
