import GowersSzemeredi.Proofs18CoverExplicit
import GowersSzemeredi.Proofs18CoverFejerAllDegrees
import GowersSzemeredi.Proofs18LengthSixSzemeredi
import GowersSzemeredi.Proofs13ContextExtraction
import GowersSzemeredi.Proofs13ExplicitFourierExponent
import GowersSzemeredi.Proofs13OddFourierSquare
import GowersSzemeredi.Proofs13PurifiedContext
import GowersSzemeredi.Proofs13SmallIntegerSquare
import GowersSzemeredi.Proofs13PolyRowExponent
import GowersSzemeredi.Proofs13ExplicitOddSquare
import GowersSzemeredi.Proofs17ExplicitCubicLocalization
import GowersSzemeredi.Proofs18CubicDiscrepancy
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LeanProofs.GowersSzemeredi.FinalInputs.hyp,
      ``LeanProofs.GowersSzemeredi.FinalInputs.cover,
      ``LeanProofs.GowersSzemeredi.FinalInputs.covers,
      ``LeanProofs.GowersSzemeredi.FinalInputs.theorem_16_2_polynomial,
      ``LeanProofs.GowersSzemeredi.exp_exp_le_two_rpow_two_rpow,
      ``LeanProofs.GowersSzemeredi.exp_exp_pow_le_two_rpow_two_rpow,
      ``LeanProofs.GowersSzemeredi.interval_exponent_le,
      ``LeanProofs.GowersSzemeredi.closedThreshold_le_of_env,
      ``LeanProofs.GowersSzemeredi.inv_thr_le_ex_of_partition_bound,
      ``LeanProofs.GowersSzemeredi.inv_thr_le_ex_sharp,
      ``LeanProofs.GowersSzemeredi.quadraticIntervalClosedThreshold_le_explicit_tower,
      ``LeanProofs.GowersSzemeredi.fejerFiveTermThreshold_le_explicit_tower,
      ``LeanProofs.GowersSzemeredi.lengthSixClosedThreshold_le_source,
      ``LeanProofs.GowersSzemeredi.roth_threshold_le_szemerediThreshold,
      ``LeanProofs.GowersSzemeredi.roth_threshold_le_szemerediThresholdAt_three,
      ``LeanProofs.GowersSzemeredi.roth_threshold_le_szemerediThresholdAt_four,
      ``LeanProofs.GowersSzemeredi.roth_threshold_le_szemerediThresholdAt_five,
      ``LeanProofs.GowersSzemeredi.roth_threshold_le_szemerediThresholdAt_six,
      ``LeanProofs.GowersSzemeredi.genMuX_le,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_L5_all_of_profiles_cover,
      ``LeanProofs.GowersSzemeredi.genMuXK3_fit,
      ``LeanProofs.GowersSzemeredi.polyGenMuJT3_fit,
      ``LeanProofs.GowersSzemeredi.classCovers_of_profiles,
      ``LeanProofs.GowersSzemeredi.envelope_induction,
      ``LeanProofs.GowersSzemeredi.envBound_allC,
      ``LeanProofs.GowersSzemeredi.polyEnvBound_allC,
      ``LeanProofs.GowersSzemeredi.envBound_allT,
      ``LeanProofs.GowersSzemeredi.polyEnvBound_allT,
      ``LeanProofs.GowersSzemeredi.envBound_allX,
      ``LeanProofs.GowersSzemeredi.envBound_allXF,
      ``LeanProofs.GowersSzemeredi.polyEnvBound_allF,
      ``LeanProofs.GowersSzemeredi.FinalInputs.envBound,
      ``LeanProofs.GowersSzemeredi.FinalInputs.polyEnvBound,
      ``LeanProofs.GowersSzemeredi.FinalInputs.corollary_16_11_polynomial,
      ``LeanProofs.GowersSzemeredi.double_exp_le_szemerediThresholdAt,
      ``LeanProofs.GowersSzemeredi.theorem182AtSharp_of_envBound,
      ``LeanProofs.GowersSzemeredi.double_exp_le_szemerediThreshold,
      ``LeanProofs.GowersSzemeredi.theorem182At_of_envBound,
      ``LeanProofs.GowersSzemeredi.inv_thr_le_ex,
      ``LeanProofs.GowersSzemeredi.section16RecurrenceProfileWith_explicit,
      ``LeanProofs.GowersSzemeredi.explicit_family_constants_le,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_explicit,
      ``LeanProofs.GowersSzemeredi.corollary_18_7_explicit,
      ``LeanProofs.GowersSzemeredi.theorem_1_2_explicit,
      ``LeanProofs.GowersSzemeredi.theorem_1_3_explicit,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_L3,
      ``LeanProofs.GowersSzemeredi.van_der_waerden_L3_all,
      ``LeanProofs.GowersSzemeredi.van_der_waerden_L0_thirteen_le,
      ``LeanProofs.GowersSzemeredi.section13_prepared_frequency_graph,
      ``LeanProofs.GowersSzemeredi.context_arrangementCount_le_card_pow,
      ``LeanProofs.GowersSzemeredi.section13SquareExponent_ge_spectral_power,
      ``LeanProofs.GowersSzemeredi.exists_odd_nat_between_half,
      ``LeanProofs.GowersSzemeredi.lemma_13_11_holds,
      ``LeanProofs.GowersSzemeredi.theorem_13_12_with_explicit_bound,
      ``LeanProofs.GowersSzemeredi.theorem_13_12_odd_square,
      ``LeanProofs.GowersSzemeredi.cubic_nonuniformity_localized_phase_removal_with_upper,
      ``LeanProofs.GowersSzemeredi.explicit_family_constants_poly_le,
      ``LeanProofs.GowersSzemeredi.theorem_18_1_d4,
      ``LeanProofs.GowersSzemeredi.theorem_18_1_d3_eight_le,
      ``LeanProofs.GowersSzemeredi.theorem_18_1_d2_eleven_le,
      ``LeanProofs.GowersSzemeredi.theorem_18_1_d4_implies_printed,
      ``LeanProofs.GowersSzemeredi.corollary_18_7_L3,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_L3_implies_printed,
      ``LeanProofs.GowersSzemeredi.corollary_18_7_L3_implies_printed,
      ``LeanProofs.GowersSzemeredi.theorem_1_3_L3,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_L2_eight_le,
      ``LeanProofs.GowersSzemeredi.corollary_18_7_L2_eight_le,
      ``LeanProofs.GowersSzemeredi.van_der_waerden_L2_eight_le,
      ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_eight_le,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_L1_eleven_le,
      ``LeanProofs.GowersSzemeredi.corollary_18_7_L1_eleven_le,
      ``LeanProofs.GowersSzemeredi.van_der_waerden_L1_eleven_le,
      ``LeanProofs.GowersSzemeredi.theorem_1_3_L1_eleven_le,
      ``LeanProofs.GowersSzemeredi.theorem_18_2_L0_thirteen_le,
      ``LeanProofs.GowersSzemeredi.corollary_18_7_L0_thirteen_le,
      ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_thirteen_le,
      ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerT3,
      ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerJT3] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the shared double-exponential conversions and phase-refinement estimates, uniform long-progression envelope bound, shared envelope induction and cover setup, threshold conversion, recurrence inputs, original final quantitative theorem, all 25 consolidated stronger-bound theorems and Section 13 compatibility theorems with only approved axioms."
