import LeSaulnierVijay2010
import LeSaulnierVijay2011.Proofs

/-!
# Proofs for LeSaulnier--Vijay (2010)

The arXiv preprint and journal article have the same established mathematical
core.  This module reuses the journal-version proofs whenever the catalogued
propositions coincide, while retaining the preprint namespace and statement
names.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.LeSaulnierVijay2010

theorem M_four_value_holds : M_four_value :=
  LeanProofs.RamseyPaperCommon.lesaulnier2010_M_four_value

theorem M_four_representatives_holds : M_four_representatives :=
  LeanProofs.RamseyPaperCommon.lesaulnier2010_M_four_representatives

theorem M_initial_values_holds : M_initial_values :=
  LeanProofs.RamseyPaperCommon.lesaulnier2010_M_initial_values

theorem davis_counting_bounds_holds : davis_counting_bounds := by
  simpa [davis_counting_bounds,
    LeanProofs.LeSaulnierVijay2011.davis_counting_bounds] using
    LeanProofs.LeSaulnierVijay2011.davis_counting_bounds_holds

theorem sharma_superpolynomial_lower_bound_holds :
    sharma_superpolynomial_lower_bound := by
  simpa [sharma_superpolynomial_lower_bound,
    LeanProofs.LeSaulnierVijay2011.sharma_superpolynomial_lower_bound] using
    LeanProofs.LeSaulnierVijay2011.sharma_superpolynomial_lower_bound_holds

theorem M_even_recurrence_holds : M_even_recurrence := by
  simpa [M_even_recurrence,
    LeanProofs.LeSaulnierVijay2011.M_even_recurrence] using
    LeanProofs.LeSaulnierVijay2011.M_even_recurrence_holds

theorem M_odd_recurrence_holds : M_odd_recurrence := by
  simpa [M_odd_recurrence,
    LeanProofs.LeSaulnierVijay2011.M_odd_recurrence] using
    LeanProofs.LeSaulnierVijay2011.M_odd_recurrence_holds

theorem theorem_1_holds : theorem_1 := by
  simpa [theorem_1, theorem1Constant,
    LeanProofs.LeSaulnierVijay2011.theorem_1,
    LeanProofs.LeSaulnierVijay2011.theorem1Constant] using
    LeanProofs.LeSaulnierVijay2011.theorem_1_holds

theorem M_ratio_does_not_tend_to_two_holds : M_ratio_does_not_tend_to_two := by
  simpa [M_ratio_does_not_tend_to_two,
    LeanProofs.LeSaulnierVijay2011.M_ratio_does_not_tend_to_two] using
    LeanProofs.LeSaulnierVijay2011.M_ratio_does_not_tend_to_two_holds

theorem every_permutation_of_positives_has_three_AP_holds :
    every_permutation_of_positives_has_three_AP := by
  simpa [every_permutation_of_positives_has_three_AP,
    LeanProofs.LeSaulnierVijay2011.every_permutation_of_positives_has_three_AP] using
    LeanProofs.LeSaulnierVijay2011.every_permutation_of_positives_has_three_AP_holds

theorem theorem_2_finite_claim_holds : theorem_2_finite_claim := by
  simpa [theorem_2_finite_claim,
    LeanProofs.LeSaulnierVijay2011.theorem_2_finite_claim] using
    LeanProofs.LeSaulnierVijay2011.theorem_2_finite_claim_holds

theorem theorem_2_block_cardinalities_holds : theorem_2_block_cardinalities := by
  intro i hi
  obtain ⟨heven, hodd⟩ :=
    LeanProofs.LeSaulnierVijay2011.theorem_2_block_cardinalities_holds i hi
  constructor
  · exact heven
  · rw [hodd, show 2 * i - 2 = 2 * (i - 1) by omega, pow_mul]
    norm_num

theorem theorem_2_blocks_cover_positive_integers_holds :
    theorem_2_blocks_cover_positive_integers := by
  simpa [theorem_2_blocks_cover_positive_integers,
    LeanProofs.LeSaulnierVijay2011.theorem_2_blocks_cover_positive_integers] using
    LeanProofs.LeSaulnierVijay2011.theorem_2_blocks_cover_positive_integers_holds

theorem theorem_2_blocks_pairwise_disjoint_holds :
    theorem_2_blocks_pairwise_disjoint := by
  simpa [theorem_2_blocks_pairwise_disjoint,
    LeanProofs.LeSaulnierVijay2011.theorem_2_blocks_pairwise_disjoint] using
    LeanProofs.LeSaulnierVijay2011.theorem_2_blocks_pairwise_disjoint_holds

theorem theorem_2_odd_even_separation_holds : theorem_2_odd_even_separation := by
  simpa [theorem_2_odd_even_separation,
    LeanProofs.LeSaulnierVijay2011.theorem_2_odd_even_separation] using
    LeanProofs.LeSaulnierVijay2011.theorem_2_odd_even_separation_holds

theorem theorem_2_block_concatenation_is_odd_four_avoiding_holds :
    theorem_2_block_concatenation_is_odd_four_avoiding := by
  simpa [theorem_2_block_concatenation_is_odd_four_avoiding,
    LeanProofs.LeSaulnierVijay2011.theorem_2_block_concatenation_is_odd_four_avoiding,
    Theorem2BlocksInOrder, LeanProofs.LeSaulnierVijay2011.Theorem2BlocksInOrder] using
    LeanProofs.LeSaulnierVijay2011.theorem_2_block_concatenation_is_odd_four_avoiding_holds

theorem theorem_2_holds : theorem_2 := by
  simpa [theorem_2, LeanProofs.LeSaulnierVijay2011.theorem_2] using
    LeanProofs.LeSaulnierVijay2011.theorem_2_holds

theorem positive_integers_are_five_avoidable_holds :
    positive_integers_are_five_avoidable := by
  simpa [positive_integers_are_five_avoidable,
    LeanProofs.LeSaulnierVijay2011.positive_integers_are_five_avoidable] using
    LeanProofs.LeSaulnierVijay2011.positive_integers_are_five_avoidable_holds

theorem alpha_beta_of_five_or_more_holds : alpha_beta_of_five_or_more := by
  simpa [alpha_beta_of_five_or_more,
    LeanProofs.LeSaulnierVijay2011.alpha_beta_of_five_or_more] using
    LeanProofs.LeSaulnierVijay2011.alpha_beta_of_five_or_more_holds

theorem geometricBlock_cross_gap_holds : geometricBlock_cross_gap := by
  simpa [geometricBlock_cross_gap,
    LeanProofs.LeSaulnierVijay2011.geometricBlock_cross_gap] using
    LeanProofs.LeSaulnierVijay2011.geometricBlock_cross_gap_holds

theorem geometricBlock_concatenation_is_four_avoiding_holds :
    geometricBlock_concatenation_is_four_avoiding := by
  simpa [geometricBlock_concatenation_is_four_avoiding,
    LeanProofs.LeSaulnierVijay2011.geometricBlock_concatenation_is_four_avoiding,
    BlocksInOrder, LeanProofs.LeSaulnierVijay2011.BlocksInOrder] using
    LeanProofs.LeSaulnierVijay2011.geometricBlock_concatenation_is_four_avoiding_holds

theorem geometricSet_is_four_avoidable_holds : geometricSet_is_four_avoidable := by
  simpa [geometricSet_is_four_avoidable,
    LeanProofs.LeSaulnierVijay2011.geometricSet_is_four_avoidable] using
    LeanProofs.LeSaulnierVijay2011.geometricSet_is_four_avoidable_holds

theorem geometricSet_densities_holds : geometricSet_densities := by
  simpa [geometricSet_densities,
    LeanProofs.LeSaulnierVijay2011.geometricSet_densities] using
    LeanProofs.LeSaulnierVijay2011.geometricSet_densities_holds

theorem p_closed_form_holds : p_closed_form := by
  simpa [p_closed_form, LeanProofs.LeSaulnierVijay2011.p_closed_form] using
    LeanProofs.LeSaulnierVijay2011.p_closed_form_holds

theorem TBlock_cross_gap_holds : TBlock_cross_gap := by
  simpa [TBlock_cross_gap, LeanProofs.LeSaulnierVijay2011.TBlock_cross_gap] using
    LeanProofs.LeSaulnierVijay2011.TBlock_cross_gap_holds

theorem TBlock_same_block_gap_holds : TBlock_same_block_gap := by
  simpa [TBlock_same_block_gap,
    LeanProofs.LeSaulnierVijay2011.TBlock_same_block_gap] using
    LeanProofs.LeSaulnierVijay2011.TBlock_same_block_gap_holds

theorem TBlock_concatenation_is_three_avoiding_holds :
    TBlock_concatenation_is_three_avoiding := by
  simpa [TBlock_concatenation_is_three_avoiding,
    LeanProofs.LeSaulnierVijay2011.TBlock_concatenation_is_three_avoiding,
    BlocksInOrder, LeanProofs.LeSaulnierVijay2011.BlocksInOrder] using
    LeanProofs.LeSaulnierVijay2011.TBlock_concatenation_is_three_avoiding_holds

theorem TSet_is_three_avoidable_holds : TSet_is_three_avoidable := by
  simpa [TSet_is_three_avoidable,
    LeanProofs.LeSaulnierVijay2011.TSet_is_three_avoidable] using
    LeanProofs.LeSaulnierVijay2011.TSet_is_three_avoidable_holds

theorem TSet_densities_holds : TSet_densities := by
  simpa [TSet_densities, LeanProofs.LeSaulnierVijay2011.TSet_densities] using
    LeanProofs.LeSaulnierVijay2011.TSet_densities_holds

theorem theorem_3_holds : theorem_3 := by
  simpa [theorem_3, LeanProofs.LeSaulnierVijay2011.theorem_3] using
    LeanProofs.LeSaulnierVijay2011.theorem_3_holds

theorem alpha_beta_sum_obstructs_partition_holds : alpha_beta_sum_obstructs_partition := by
  simpa [alpha_beta_sum_obstructs_partition,
    LeanProofs.LeSaulnierVijay2011.alpha_beta_sum_obstructs_partition,
    erdos_graham_partition_question,
    LeanProofs.LeSaulnierVijay2011.erdos_graham_partition_question] using
    LeanProofs.LeSaulnierVijay2011.alpha_beta_sum_obstructs_partition_holds

end LeanProofs.LeSaulnierVijay2010
