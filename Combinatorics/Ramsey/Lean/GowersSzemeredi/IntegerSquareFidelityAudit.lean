import GowersSzemeredi.RectangleFidelityAudit
import GowersSzemeredi.Proofs13IntegerPrintedTheorem
import Lean.Util.CollectAxioms

/-! Genuine integer-square Theorem 13.12, with its original numerical
bounds and an exact-type and complete transitive-axiom audit. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.clampedCoverIndex_isProper,
    ``LeanProofs.GowersSzemeredi.clampedCoverIndex_subset,
    ``LeanProofs.GowersSzemeredi.clampedCoverIndex_covers,
    ``LeanProofs.GowersSzemeredi.NatAP.clampedCover_properties,
    ``LeanProofs.GowersSzemeredi.NatAP.clampedCover_covers,
    ``LeanProofs.GowersSzemeredi.NatAP.clampedCover_mod_covers,
    ``LeanProofs.GowersSzemeredi.clampedCover_capacity,
    ``LeanProofs.GowersSzemeredi.dense_equal_integer_square,
    ``LeanProofs.GowersSzemeredi.dense_common_step_integer_square,
    ``LeanProofs.GowersSzemeredi.integer_square_width_absorption,
    ``LeanProofs.GowersSzemeredi.power_density_sixteen_loss,
    ``LeanProofs.GowersSzemeredi.section13_integer_extraction_parameter_bounds,
    ``LeanProofs.GowersSzemeredi.integer_square_raw_length_four,
    ``LeanProofs.GowersSzemeredi.ModAP.step_ne_zero_of_proper_two,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_integer_all_prime,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_integer_representatives_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  let info ← getConstInfo ``LeanProofs.GowersSzemeredi.theorem_13_12_integer_representatives_holds
  unless info.type == mkConst ``LeanProofs.GowersSzemeredi.theorem_13_12_integer_representatives do
    throwError "The genuine integer-square companion does not prove its exact statement"
  logInfo "Checked sixteen integer-square results and exact genuine Theorem 13.12; only approved axioms."
