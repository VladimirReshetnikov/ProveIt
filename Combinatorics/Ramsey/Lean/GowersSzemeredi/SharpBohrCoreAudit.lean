import GowersSzemeredi.Proofs07SharpBohr
import GowersSzemeredi.Proofs07CoordinateLinearity
import Lean.Util.CollectAxioms

example : LeanProofs.GowersSzemeredi.lemma_7_7_original_radius :=
  LeanProofs.GowersSzemeredi.lemma_7_7_original_radius_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let positive : Array Name := #[
    ``LeanProofs.GowersSzemeredi.translation_fiber_sum,
    ``LeanProofs.GowersSzemeredi.exists_translation_fiber_cross_bound,
    ``LeanProofs.GowersSzemeredi.finite_product_subset_card,
    ``LeanProofs.GowersSzemeredi.bohr_card_lower_bound_sharp,
    ``LeanProofs.GowersSzemeredi.bohr_nonzero_of_sharp_radius,
    ``LeanProofs.GowersSzemeredi.bohr_nonzero_of_original_radius,
    ``LeanProofs.GowersSzemeredi.lemma_7_7_original_radius_holds
  ]
  let refutations : Array Name := #[
    ``LeanProofs.GowersSzemeredi.bohr_unrestricted_radius_counterexample,
    ``LeanProofs.GowersSzemeredi.progression_coordinate_linearity_counterexample
  ]
  for name in positive ++ refutations do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked seven translated-box/Bohr results and two separate scope refutations; only approved axioms."
