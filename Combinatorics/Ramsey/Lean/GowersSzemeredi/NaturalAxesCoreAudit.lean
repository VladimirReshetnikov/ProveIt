import GowersSzemeredi.Proofs13SharedIntegerStep
import GowersSzemeredi.Proofs13SparseNaturalAxes
import Lean.Util.CollectAxioms

/-! Explicit ordinary axes with a shared positive integer step. The separate
refutation concerns the weaker geometric implication, not Theorem13.12. -/

example : LeanProofs.GowersSzemeredi.theorem_13_12_natural_axes :=
  LeanProofs.GowersSzemeredi.theorem_13_12_natural_axes_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.NatAP.carrier_subset_range_of_terms,
    ``LeanProofs.GowersSzemeredi.NatAP.bounded_axis_certificate,
    ``LeanProofs.GowersSzemeredi.adjacentIntegerAP_nat_properties,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_natural_small,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_natural_near_one,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_natural_all_prime,
    ``LeanProofs.GowersSzemeredi.NaturalFourierSquare.to_modular,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_natural_axes_holds,
    ``LeanProofs.GowersSzemeredi.intervalThrough_nat_properties,
    ``LeanProofs.GowersSzemeredi.natural_square_of_one_point_budget,
    ``LeanProofs.GowersSzemeredi.corollary_13_10_printed_natural_of_one_point_budget,
    ``LeanProofs.GowersSzemeredi.corollary_13_10_printed_natural_small_modulus
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  let counter := ``LeanProofs.GowersSzemeredi.equal_modular_steps_separate_integer_axes_counterexample
  for axiomName in (← collectAxioms counter) do
    unless allowed.contains axiomName do
      throwError "{counter} depends on unapproved axiom {axiomName}"
  logInfo "Checked twelve natural-axis results and a separate weaker-geometry counterexample; only approved axioms."
