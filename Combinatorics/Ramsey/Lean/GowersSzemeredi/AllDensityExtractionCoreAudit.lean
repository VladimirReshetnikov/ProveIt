import GowersSzemeredi.Proofs13PrintedAllDensities
import Lean.Util.CollectAxioms

/-! Exact statement and axiom checks of the original printed numerical
Lemma13.6 at every density. Modular properness is retained; this gate does
not certify additional integer geometry in every intermediate progression. -/

example : LeanProofs.GowersSzemeredi.lemma_13_6_printed_bounds :=
  LeanProofs.GowersSzemeredi.lemma_13_6_printed_bounds_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.finite_common_point_of_small_complements,
    ``LeanProofs.GowersSzemeredi.finite_two_common_points_of_small_complements,
    ``LeanProofs.GowersSzemeredi.finite_common_shift_of_small_complement,
    ``LeanProofs.GowersSzemeredi.dense_freiman_two_affine_extension,
    ``LeanProofs.GowersSzemeredi.dense_freiman_two_linear,
    ``LeanProofs.GowersSzemeredi.dense_freiman_eight_linear,
    ``LeanProofs.GowersSzemeredi.four_large_domains_common_columns,
    ``LeanProofs.GowersSzemeredi.horizontalSection_card_eq_fiber,
    ``LeanProofs.GowersSzemeredi.sum_horizontalSection_card,
    ``LeanProofs.GowersSzemeredi.section13_bad_rows_bound,
    ``LeanProofs.GowersSzemeredi.section13_dense_rows_large,
    ``LeanProofs.GowersSzemeredi.section13_dense_row_piece_mass,
    ``LeanProofs.GowersSzemeredi.section13_dense_rows_affine,
    ``LeanProofs.GowersSzemeredi.section13_dense_row_coefficients_freiman_two,
    ``LeanProofs.GowersSzemeredi.section13_dense_row_piece_bilinear,
    ``LeanProofs.GowersSzemeredi.finite_shift_overlap_card,
    ``LeanProofs.GowersSzemeredi.section13_dense_row_edges_mass,
    ``LeanProofs.GowersSzemeredi.bilinear_vertical_difference_rule,
    ``LeanProofs.GowersSzemeredi.section13_printed_high_density_edge_rules,
    ``LeanProofs.GowersSzemeredi.section13Zeta_le_half,
    ``LeanProofs.GowersSzemeredi.section13_ten_target_le_one_small_modulus,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_high_density_from_budgets,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_all_densities_improved_length,
    ``LeanProofs.GowersSzemeredi.lemma_13_6_printed_bounds_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked24 dense-extension and original all-density extraction results; only approved axioms."
