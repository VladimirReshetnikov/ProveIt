import GRHArticle.ProgressionFree.EulerLowerBound
import GRHArticle.ProgressionFree.ExplicitExponentBound
import GRHArticle.ProgressionFree.ExplicitWeightCast
import GRHArticle.ProgressionFree.FourMarkerMass

/-!
# Density gain for the four-marker construction on primes through 1427

The finite scaled reciprocal-mass check gives a gap uniform in the exponent
cutoff. The common rough factor has its own positive lower bound, uniform
in the prime cutoff. The resulting quantitative gap survives the passage
to the two natural densities.
-/

open Filter
open scoped BigOperators Topology

namespace GRHArticle.ProgressionFree

private theorem explicitOddPrimes_prime (p : ℕ) (hp : p ∈ explicitOddPrimes) : p.Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hp)

private theorem two_not_mem_explicitOddPrimes : 2 ∉ explicitOddPrimes :=
  Finset.notMem_erase _ _

private theorem explicitPrimeProduct_pos : 0 < (explicitOddPrimeProduct : ℝ) := by
  exact Nat.cast_pos.mpr (Finset.prod_pos fun p hp => (explicitOddPrimes_prime p hp).pos)

private theorem explicit_insert_two : insert 2 explicitOddPrimes = explicitPrimes :=
  Finset.insert_erase (Nat.mem_primesLE.mpr ⟨by decide, Nat.prime_two⟩)

private theorem half_mass_lower (K : ℕ) (hK : 14 < K) :
    (9 : ℝ) / 100000 / (explicitOddPrimeProduct : ℝ) <
      exactPatternMass (1 / 2) explicitSatelliteWeight (fourMarkerExponentSet ↥explicitOddPrimes) K -
      exactPatternMass (1 / 2) explicitSatelliteWeight (rankinExactExponentSet ↥explicitOddPrimes) K := by
  have hu (p : ↥explicitOddPrimes) : 0 ≤ explicitSatelliteWeight p :=
    one_div_nonneg.mpr (Nat.cast_nonneg _)
  have hMass := fourMarker_exactPatternMass_sub_ge explicitSatelliteWeight hu hK
    (greedyExponentsBelow_half_mass_le_upsilon K)
  dsimp only at hMass
  rw [explicitSatelliteWeight_prod, explicit_scaledGain_eq_real] at hMass
  have hcert : (9 : ℝ) / 100000 < (explicitScaledGain : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr explicit_scaledMass_gt
  calc
    _ = (1 / (explicitOddPrimeProduct : ℝ)) * (9 / 100000) := by ring
    _ < (1 / (explicitOddPrimeProduct : ℝ)) * (explicitScaledGain : ℝ) :=
      mul_lt_mul_of_pos_left hcert (one_div_pos.mpr explicitPrimeProduct_pos)
    _ ≤ _ := hMass

private theorem positive_local_normalization {p : ℕ} (hp : p.Prime) :
    0 < 1 - 1 / (p : ℝ) := by
  have hp₁ : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((div_lt_iff₀ (by linarith only [hp₁])).mpr (by linarith only [hp₁]))

private theorem bounded_rough_factor_lower {p K : ℕ} (hp : p.Prime) (hK : 1 < K) :
    1 - 1 / (p : ℝ) ^ 2 ≤
      (1 - 1 / (p : ℝ)) * ∑ a ∈ greedyExponentsBelow K, (1 / (p : ℝ)) ^ a := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ greedyExponentsBelow K := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact mem_greedyExponentsBelow.mpr ⟨zero_mem_greedyExponents, by omega⟩
    · exact mem_greedyExponentsBelow.mpr ⟨one_mem_greedyExponents, hK⟩
  have hone : 1 + 1 / (p : ℝ) ≤ ∑ a ∈ greedyExponentsBelow K, (1 / (p : ℝ)) ^ a := by
    simpa using Finset.sum_le_sum_of_subset_of_nonneg (f := fun a : ℕ => (1 / (p : ℝ)) ^ a)
      hsub (fun a _ _ => pow_nonneg (by positivity) _)
  calc
    _ = (1 - 1 / (p : ℝ)) * (1 + 1 / (p : ℝ)) := by rw [← one_div_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hone (positive_local_normalization hp).le

private theorem commonWeight_gt_one_fifteenth (Y K : ℕ) (hK : 1 < K) :
    (1 : ℝ) / 15 < exactRuleCommonWeight (exchangeAffected 2 explicitOddPrimes)
      (Subtype.val : ↥(exchangeRough 2 explicitOddPrimes Y) → ℕ) K := by
  let R := exchangeRough 2 explicitOddPrimes Y
  let A := ∏ o : Option ↥explicitOddPrimes, (1 - 1 / (exchangeAffected 2 explicitOddPrimes o : ℝ))
  have hA : A = ∏ p ∈ explicitPrimes, (1 - 1 / (p : ℝ)) := by
    unfold A
    rw [Fintype.prod_option]
    change (1 - 1 / (2 : ℝ)) * ∏ p : ↥explicitOddPrimes, (1 - 1 / (p.val : ℝ)) = _
    rw [Finset.univ_eq_attach, Finset.prod_attach explicitOddPrimes (fun p : ℕ => 1 - 1 / (p : ℝ)),
      ← explicit_insert_two, Finset.prod_insert two_not_mem_explicitOddPrimes]
    rfl
  have hA₀ : 0 ≤ A := Finset.prod_nonneg fun o _ =>
    (positive_local_normalization (exchangeAffected_prime Nat.prime_two explicitOddPrimes_prime o)).le
  have hgt (p : ℕ) (hp : p ∈ R) : 1427 < p := by
    have hmem := Finset.mem_sdiff.mp hp
    apply lt_of_not_ge
    intro hle
    exact hmem.2 (explicit_insert_two.symm ▸
      Nat.mem_primesLE.mpr ⟨hle, Nat.prime_of_mem_primesLE hmem.1⟩)
  have hR₀ : (1427 / 1428 : ℝ) ≤ ∏ p : ↥R, (1 - 1 / (p.val : ℝ) ^ 2) := by
    rw [Finset.univ_eq_attach, Finset.prod_attach R (fun p : ℕ => 1 - 1 / (p : ℝ) ^ 2)]
    have h := le_prod_one_sub_inv_sq_of_lt 1427 (by decide) R hgt
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hR : (1427 / 1428 : ℝ) ≤ ∏ p : ↥R, (1 - 1 / (p.val : ℝ)) *
      ∑ a ∈ greedyExponentsBelow K, (1 / (p.val : ℝ)) ^ a := by
    refine hR₀.trans (Finset.prod_le_prod ?_ ?_)
    · intro p _
      have hp := exchangeRough_prime p
      have h₀ : 0 ≤ 1 / (p.val : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg _)
      have h₁ := (sub_pos.mp (positive_local_normalization hp)).le
      rw [← one_div_pow]
      exact sub_nonneg.mpr (by simpa using pow_le_pow_left₀ h₀ h₁ 2)
    · intro p _
      exact bounded_rough_factor_lower (exchangeRough_prime p) hK
  have hcert : (1 : ℝ) / 15 < (1427 / 1428 : ℝ) *
      ∏ p ∈ explicitPrimes, (1 - 1 / (p : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_natCast] using (Rat.cast_lt (K := ℝ)).mpr explicit_roughFactor_gt
  calc
    _ < A * (1427 / 1428) := by rw [hA, mul_comm]; exact hcert
    _ ≤ _ := mul_le_mul_of_nonneg_left hR hA₀

private noncomputable def uniformDensityGap : ℝ :=
  ((9 : ℝ) / 100000 / (3 * (10 : ℝ) ^ 590)) * (1 / 15)

private theorem one_div_ten_pow_lt_uniformGap : 1 / (10 : ℝ) ^ 596 < uniformDensityGap := by
  have hp : (10 : ℝ) ^ 596 = (10 : ℝ) ^ 6 * (10 : ℝ) ^ 590 := by rw [← pow_add]
  rw [hp]
  unfold uniformDensityGap
  calc
    _ = (1 / (10 : ℝ) ^ 6) / (10 : ℝ) ^ 590 := (div_div (1 : ℝ) ((10 : ℝ) ^ 6) ((10 : ℝ) ^ 590)).symm
    _ < ((9 : ℝ) / 100000 / 3 * (1 / 15)) / (10 : ℝ) ^ 590 :=
      div_lt_div_of_pos_right (by norm_num) (pow_pos (by norm_num) _)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

private theorem bounded_exactDensityGap_gt (Y K : ℕ) (hK : 14 < K) :
    uniformDensityGap <
      (exactPatternMass (1 / 2) explicitSatelliteWeight (fourMarkerExponentSet ↥explicitOddPrimes) K -
        exactPatternMass (1 / 2) explicitSatelliteWeight (rankinExactExponentSet ↥explicitOddPrimes) K) *
      exactRuleCommonWeight (exchangeAffected 2 explicitOddPrimes)
        (Subtype.val : ↥(exchangeRough 2 explicitOddPrimes Y) → ℕ) K := by
  have hQ : (explicitOddPrimeProduct : ℝ) < 3 * (10 : ℝ) ^ 590 := by
    exact_mod_cast explicitOddPrimeProduct_lt
  have hB : (9 : ℝ) / 100000 / (3 * (10 : ℝ) ^ 590) <
      (9 : ℝ) / 100000 / (explicitOddPrimeProduct : ℝ) :=
    div_lt_div_of_pos_left (by norm_num) explicitPrimeProduct_pos hQ
  have hL := half_mass_lower K hK
  have hMassNonneg : (0 : ℝ) ≤ _ := (div_pos (by norm_num : (0 : ℝ) < 9 / 100000)
    explicitPrimeProduct_pos).le.trans hL.le
  exact (mul_lt_mul_of_pos_right (hB.trans hL) (by norm_num : (0 : ℝ) < 1 / 15)).trans_le
    (mul_le_mul_of_nonneg_left (commonWeight_gt_one_fifteenth Y K (by omega)).le hMassNonneg)

private theorem gap_gt_of_two_errors {dR dE r e target bound : ℝ}
    (hpos : target < bound) (hgap : bound < e - r)
    (hR : |dR - r| ≤ (bound - target) / 4) (hE : |dE - e| ≤ (bound - target) / 4) :
    target < dE - dR := by
  linarith only [hpos, hgap, (abs_le.mp hR).2, (abs_le.mp hE).1]

/-- The article's specified 225-prime counterexample. It avoids all nontrivial
rational-ratio triples and its true density gain exceeds `10⁻⁵⁹⁶`. -/
theorem fourMarkerExchange1427_strictNaturalDensityGain :
    ThreeGPFree (fourMarkerExchangeSet explicitOddPrimes) ∧
    ∃ dR dE : ℝ, HasNaturalDensity rankinSet dR ∧
      HasNaturalDensity (fourMarkerExchangeSet explicitOddPrimes) dE ∧
      1 / (10 : ℝ) ^ 596 < dE - dR := by
  let S := explicitOddPrimes
  let C := rankinExactExponentSet ↥S
  let E := fourMarkerExponentSet ↥S
  let a := exchangeAffected 2 S
  let ε := (uniformDensityGap - 1 / (10 : ℝ) ^ 596) / 4
  have hε : 0 < ε := div_pos (sub_pos.mpr one_div_ten_pow_lt_uniformGap) (by norm_num)
  obtain ⟨dR, hR⟩ := exists_hasNaturalDensity_exactValuationRuleSet C Nat.prime_two
    explicitOddPrimes_prime two_not_mem_explicitOddPrimes
  obtain ⟨dE, hE⟩ := exists_hasNaturalDensity_exactValuationRuleSet E Nat.prime_two
    explicitOddPrimes_prime two_not_mem_explicitOddPrimes
  obtain ⟨Y, L, hY, _, hmY, hSY, herror⟩ := exists_digitRule_cutoffs 2 S hε
  let K := 3 * max L 5
  have hK : 14 < K := by dsimp [K]; omega
  have hKle : 3 * L ≤ K := by dsimp [K]; omega
  have herrorK : 1 / (Y : ℝ) + ∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ) ^ K ≤ ε := by
    have hsum : (∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ) ^ K) ≤
        ∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ) ^ (3 * L) := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_pow_le_one_div_pow_of_le
        (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le) hKle
    exact (add_le_add (le_refl (1 / (Y : ℝ))) hsum).trans herror
  let r := (Subtype.val : ↥(exchangeRough 2 S Y) → ℕ)
  let W := exactRuleCommonWeight a r K
  let M (B : Set (ℕ × (↥S → ℕ))) := exactPatternMass (1 / 2) explicitSatelliteWeight B K
  have hclose (B : Set (ℕ × (↥S → ℕ))) (d : ℝ)
      (hd : HasNaturalDensity (exactValuationRuleSet 2 S B) d) : |d - M B * W| ≤ ε := by
    have hf : HasNaturalDensity (finiteExactRuleSet a r B K) (M B * W) :=
      hasNaturalDensity_finiteExactRuleSet a r B K (exchangePrimeCoordinates_injective
        two_not_mem_explicitOddPrimes) (exchangeAffected_prime Nat.prime_two explicitOddPrimes_prime)
        exchangeRough_prime
    unfold HasNaturalDensity at hd hf
    exact le_of_tendsto' (hd.sub hf).abs fun N =>
      (abs_densityUpTo_exactRule_sub_trunc_le B N Nat.prime_two explicitOddPrimes_prime
        hmY hSY hY).trans herrorK
  have hgap : uniformDensityGap < M E * W - M C * W := by
    rw [← sub_mul]
    exact bounded_exactDensityGap_gt Y K hK
  have htrue : 1 / (10 : ℝ) ^ 596 < dE - dR :=
    gap_gt_of_two_errors one_div_ten_pow_lt_uniformGap hgap (hclose C dR hR) (hclose E dE hE)
  exact ⟨threeGPFree_fourMarkerExchange1427, dR, dE,
    (exactValuationRuleSet_rankin Nat.prime_two explicitOddPrimes_prime) ▸ hR, hE, htrue⟩

end GRHArticle.ProgressionFree
