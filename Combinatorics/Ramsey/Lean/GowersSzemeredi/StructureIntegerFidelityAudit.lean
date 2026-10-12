import GowersSzemeredi.FamilyLiftIntegerFidelityAudit
import GowersSzemeredi.Proofs16IntegerPrintedCorollary
import Lean.Util.CollectAxioms

/-! Genuine Theorem 16.2 and Corollary 16.11 with their printed controls,
including exact statement checks and the full transitive axiom audit. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.Box.IsAscendingInteger.coordinateReindex,
    ``LeanProofs.GowersSzemeredi.Box.HasIntegerRepresentatives.coordinateReindex,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.coordinateReindex,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.coordinateReindex_graph,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.cylAt,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.relationSum,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.relationScale,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.relSumFin,
    ``LeanProofs.GowersSzemeredi.integer_class_piece_family_cover_gen,
    ``LeanProofs.GowersSzemeredi.integer_class_piece_family_cover,
    ``LeanProofs.GowersSzemeredi.integer_class_step_cover_gen,
    ``LeanProofs.GowersSzemeredi.integer_class_step_cover,
    ``LeanProofs.GowersSzemeredi.powerUniformClass_succ_integer,
    ``LeanProofs.GowersSzemeredi.RelFreimanCover.integer_cubic_cover,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.last_cylinder,
    ``LeanProofs.GowersSzemeredi.section16_integer_poly_family_two_cover,
    ``LeanProofs.GowersSzemeredi.section16_integer_poly_piece_two_family_cover,
    ``LeanProofs.GowersSzemeredi.section16_integer_uniform_cover_two,
    ``LeanProofs.GowersSzemeredi.powerUniformClass_two_integer,
    ``LeanProofs.GowersSzemeredi.PowerUniformClass.integerCover_weaken,
    ``LeanProofs.GowersSzemeredi.powerUniformClass_all_integer,
    ``LeanProofs.GowersSzemeredi.PowerUniformClass.integerPolyCoverAt,
    ``LeanProofs.GowersSzemeredi.theorem162IntegerAt_of_integerPolyCover_tower,
    ``LeanProofs.GowersSzemeredi.PowerUniformClass.integerTheorem162At_tower,
    ``LeanProofs.GowersSzemeredi.integerMultiplyLinear_relation_dimension_zero,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_integer_zero,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_integer_representatives_holds,
    ``LeanProofs.GowersSzemeredi.Theorem162IntegerAt.restrict_function,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.dense_multilinear_box,
    ``LeanProofs.GowersSzemeredi.corollary_16_11_integer_of_dimension_induction,
    ``LeanProofs.GowersSzemeredi.corollary_16_11_integer_representatives_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  let exactStatements : Array (Name × Name) := #[
    (``LeanProofs.GowersSzemeredi.theorem_16_2_integer_representatives,
      ``LeanProofs.GowersSzemeredi.theorem_16_2_integer_representatives_holds),
    (``LeanProofs.GowersSzemeredi.corollary_16_11_integer_representatives,
      ``LeanProofs.GowersSzemeredi.corollary_16_11_integer_representatives_holds)
  ]
  for (target, proof) in exactStatements do
    let info ← getConstInfo proof
    unless info.type == mkConst target do
      throwError "{proof} does not prove exactly {target}"
  logInfo "Checked thirty-one genuine class/structure results and exact Theorem 16.2 and Corollary 16.11; only approved axioms."
