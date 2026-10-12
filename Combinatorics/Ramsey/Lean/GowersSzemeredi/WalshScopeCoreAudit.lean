import GowersSzemeredi.Proofs15BooleanAllPrimes
import GowersSzemeredi.Proofs14MomentEndpoints
import GowersSzemeredi.Proofs15DegenerateAllPrimes
import GowersSzemeredi.Proofs14_15SourceScope
import GowersSzemeredi.Proofs16PrintedSelectedMass
import GowersSzemeredi.Proofs17PrimeRange
import GowersSzemeredi.Proofs17CharacteristicTwo
import Lean.Util.CollectAxioms

example : LeanProofs.GowersSzemeredi.corollary_15_2_all_primes :=
  LeanProofs.GowersSzemeredi.corollary_15_2_all_primes_holds
example : LeanProofs.GowersSzemeredi.lemma_15_4_all_primes :=
  LeanProofs.GowersSzemeredi.lemma_15_4_all_primes_holds

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let positive : Array Name := #[
    ``LeanProofs.GowersSzemeredi.lemma_17_1_prime_range,
    ``LeanProofs.GowersSzemeredi.proposition_17_2_prime_range,
    ``LeanProofs.GowersSzemeredi.lemma_16_5_printed_mass_holds,
    ``LeanProofs.GowersSzemeredi.lemma_14_7_all_real_parameters_holds,
    ``LeanProofs.GowersSzemeredi.booleanWalsh_multiple_of_full_moment_all_primes,
    ``LeanProofs.GowersSzemeredi.corollary_15_2_all_primes_holds,
    ``LeanProofs.GowersSzemeredi.lemma_15_4_all_primes_holds
  ]
  let refutations : Array Name := #[
    ``LeanProofs.GowersSzemeredi.lemma_17_1_characteristic_two_counterexample,
    ``LeanProofs.GowersSzemeredi.lemma_17_1_characteristic_two_obstruction,
    ``LeanProofs.GowersSzemeredi.proposition_14_1_negative_alpha_counterexample,
    ``LeanProofs.GowersSzemeredi.lemma_15_1_even_prime_counterexample,
    ``LeanProofs.GowersSzemeredi.summed_slice_correlation_counterexample
  ]
  for name in positive ++ refutations do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked seven moment/Boolean/degeneracy/selected-mass/prime-range results and five separate sign, characteristic-two and proof-step refutations; only approved axioms."
