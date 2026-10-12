import GowersSzemeredi.Proofs18CoverExplicit
import GowersSzemeredi.Proofs18CoverFejerAllDegrees
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
  for name in #[``LeanProofs.GowersSzemeredi.section16RecurrenceProfileWith_explicit,
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
      ``LeanProofs.GowersSzemeredi.cubic_nonuniformity_localized_phase_removal_with_upper] do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the simplified recurrence inputs, original final quantitative theorem strengthened bounds and Section 13 compatibility theorems with only approved axioms."
