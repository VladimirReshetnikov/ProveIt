import GowersSzemeredi.RemainderIntegerFidelityAudit
import GowersSzemeredi.Proofs16IntegerFamilyPieceCover
import Lean.Util.CollectAxioms

/-! Genuine unused-coordinate lifting, sampled family interpolation and
all-scale piece covers. Their induction-provided cover inputs remain explicit. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.relation_unused_coordinate_cover,
    ``LeanProofs.GowersSzemeredi.IntegerMultiplyLinearWith.relation_lift_last,
    ``LeanProofs.GowersSzemeredi.section16_synchronize_integer_base_cover_family,
    ``LeanProofs.GowersSzemeredi.section16_synchronized_integer_compressed_cover_family,
    ``LeanProofs.GowersSzemeredi.section16_local_integer_affine_lift_family,
    ``LeanProofs.GowersSzemeredi.section16_local_integer_affine_lift_all_scales_family,
    ``LeanProofs.GowersSzemeredi.IntegerSection16LineCoverFamily.mono_count,
    ``LeanProofs.GowersSzemeredi.IntegerSection16LineCoverFamily.global_affine_lift_family,
    ``LeanProofs.GowersSzemeredi.IntegerSection16LineCoverFamily.global_affine_lift_rounded_family,
    ``LeanProofs.GowersSzemeredi.integerMultiplyLinearWith_of_large_box_covers,
    ``LeanProofs.GowersSzemeredi.integer_abstract_family_piece_large_box_profile,
    ``LeanProofs.GowersSzemeredi.integer_abstract_family_piece_cover_with
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked twelve genuine relation-lift, sampling and piece-family cover results; only approved axioms."
