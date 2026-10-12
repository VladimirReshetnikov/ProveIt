import GowersSzemeredi.IntegerFidelityAudit
import GowersSzemeredi.Proofs13AllPrimeModuli
import Lean.Util.CollectAxioms

/-! Check the removal of the extra modulus threshold from Theorem 13.12,
without claiming that the remaining integer-box conclusions are finished. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked : Array Name := #[
    ``LeanProofs.GowersSzemeredi.section13_printed_top_dominates_threshold,
    ``LeanProofs.GowersSzemeredi.rpow_small_below_double_exp,
    ``LeanProofs.GowersSzemeredi.section13_printed_width_small_below_threshold,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_integer_near_one,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_all_prime,
    ``LeanProofs.GowersSzemeredi.theorem_13_12_without_modulus_threshold_holds
  ]
  for name in checked do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  let target := ``LeanProofs.GowersSzemeredi.theorem_13_12_without_modulus_threshold
  let proof ← getConstInfo ``LeanProofs.GowersSzemeredi.theorem_13_12_without_modulus_threshold_holds
  unless proof.type == mkConst target do
    throwError "The all-prime proof does not prove exactly the threshold-free statement"
  logInfo "Checked six all-prime modulus-range theorems and the exact strengthened statement; only approved axioms."
