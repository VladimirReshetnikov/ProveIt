import GRHArticle.ProgressionFree.ExchangeDensity
import GRHArticle.ProgressionFree.PrimeReciprocalBound

/-!
# A specified initial segment for the one-digit exchange

All odd primes at most the ceiling of `exp (exp 7)` have reciprocal sum
greater than five. Therefore the exchange at marker two with precisely these
satellites has greater natural density than Rankin's set.
-/

open scoped BigOperators

namespace GRHArticle.ProgressionFree

/-- The explicit upper cutoff in the integer one-digit exchange. -/
noncomputable def explicitOneDigitExchangeCutoff : ℕ :=
  Nat.ceil (Real.exp (Real.exp 7))

/-- All odd primes at most the article's cutoff. -/
noncomputable def explicitOneDigitExchangeSatellites : Finset ℕ :=
  (Nat.primesLE explicitOneDigitExchangeCutoff).erase 2

theorem five_lt_sum_explicitOneDigitExchangeSatellites :
    5 < ∑ p ∈ explicitOneDigitExchangeSatellites, 1 / (p : ℝ) := by
  have hceil : Real.exp (Real.exp 7) ≤ (explicitOneDigitExchangeCutoff : ℝ) :=
    Nat.le_ceil _
  have hYreal : 1 < (explicitOneDigitExchangeCutoff : ℝ) :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 7)).trans_le hceil
  have hY : 1 < explicitOneDigitExchangeCutoff := by exact_mod_cast hYreal
  have hlog : Real.exp 7 ≤ Real.log (explicitOneDigitExchangeCutoff : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hceil
  have hseven : 7 ≤ Real.log (Real.log (explicitOneDigitExchangeCutoff : ℝ)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hlog
  have hsum := log_log_le_primeReciprocalSum_add_one explicitOneDigitExchangeCutoff hY
  have hmem : 2 ∈ Nat.primesLE explicitOneDigitExchangeCutoff :=
    Nat.mem_primesLE.mpr ⟨hY, Nat.prime_two⟩
  have hsplit := Finset.sum_erase_add (Nat.primesLE explicitOneDigitExchangeCutoff)
    (fun p : ℕ => (1 : ℝ) / (p : ℝ)) hmem
  change (∑ p ∈ explicitOneDigitExchangeSatellites, 1 / (p : ℝ)) + 1 / 2 =
    ∑ p ∈ Nat.primesLE explicitOneDigitExchangeCutoff, 1 / (p : ℝ) at hsplit
  linarith only [hseven, hsum, hsplit]

/-- The specified exchange set avoids all nonconstant rational-ratio triples
and has strictly greater natural density than Rankin's set. -/
theorem explicitOneDigitExchange_strictNaturalDensityGain :
    ThreeGPFree (exchangedRankinSet 2 explicitOneDigitExchangeSatellites) ∧
    ∃ dR dE : ℝ, HasNaturalDensity rankinSet dR ∧
      HasNaturalDensity (exchangedRankinSet 2 explicitOneDigitExchangeSatellites) dE ∧ dR < dE := by
  let S := explicitOneDigitExchangeSatellites
  have h₂ : 2 ∉ S := Finset.notMem_erase _ _
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)
  let u (p : ↥S) : ℝ := 1 / (p.val : ℝ)
  have hu (p : ↥S) : 0 < u p :=
    one_div_pos.mpr (Nat.cast_pos.mpr (hS p.val p.property).pos)
  have hsum : 5 < ∑ p : ↥S, u p := by
    rw [Finset.univ_eq_attach, Finset.sum_attach S (fun p : ℕ => (1 : ℝ) / (p : ℝ))]
    exact five_lt_sum_explicitOneDigitExchangeSatellites
  have hmass := (binaryDigitCap_mass_lt_exchanged_at_two_iff u hu).mpr hsum
  obtain ⟨dR, hR⟩ := exists_hasNaturalDensity_digitRuleSet (binaryDigitCap ↥S) Nat.prime_two hS h₂
  obtain ⟨dE, hE⟩ := exists_hasNaturalDensity_digitRuleSet (exchangedDigitCap ↥S)
    Nat.prime_two hS h₂
  exact ⟨threeGPFree_exchangedRankinSet 2 S Nat.prime_two hS, dR, dE,
    (digitRuleSet_binary Nat.prime_two hS) ▸ hR, (digitRuleSet_exchanged 2 S) ▸ hE,
    naturalDensity_digitRuleSet_strict_mono_mass Nat.prime_two hS h₂ hR hE hmass⟩

end GRHArticle.ProgressionFree
