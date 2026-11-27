import GRHArticle.ProgressionFree.EulerLowerBound
import GRHArticle.ProgressionFree.ExchangeApproximation

/-!
# Strict natural-density gain of the one-digit exchange

The cap masses differ by a positive amount. The finite densities multiply
this difference by a factor bounded below uniformly in both cutoffs. Uniform
counting approximation passes the strict gap to the two natural densities.
-/

open Filter
open scoped BigOperators Topology

namespace GRHArticle.ProgressionFree

private theorem prime_reciprocal_lt_one {p : ℕ} (hp : p.Prime) : 1 / (p : ℝ) < 1 := by
  have hp₁ : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  rw [div_lt_iff₀ (by linarith only [hp₁]), one_mul]
  exact hp₁

private theorem high_weight_sum_ge_one (p L : ℕ) (hL : 0 < L) :
    1 ≤ ∑ h ∈ greedyExponentsBelow L, (1 / (p : ℝ)) ^ (3 * h) := by
  have hm : 0 ∈ greedyExponentsBelow L :=
    mem_greedyExponentsBelow.mpr ⟨zero_mem_greedyExponents, hL⟩
  simpa only [Nat.mul_zero, pow_zero] using
    (Finset.single_le_sum (f := fun h : ℕ => (1 / (p : ℝ)) ^ (3 * h))
      (fun h _ => pow_nonneg (by positivity) _) hm)

private theorem rough_factor_ge_one_sub_square (p L : ℕ) (hp : p.Prime) (hL : 0 < L) :
    1 - 1 / (p : ℝ) ^ 2 ≤
      (1 - 1 / (p : ℝ)) * ∑ n ∈ greedyExponentsBelow (3 * L), (1 / (p : ℝ)) ^ n := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ greedyExponentsBelow (3 * L) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact mem_greedyExponentsBelow.mpr ⟨zero_mem_greedyExponents, by omega⟩
    · exact mem_greedyExponentsBelow.mpr ⟨one_mem_greedyExponents, by omega⟩
  have htwo : 1 + 1 / (p : ℝ) ≤
      ∑ n ∈ greedyExponentsBelow (3 * L), (1 / (p : ℝ)) ^ n := by
    simpa using Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => (1 / (p : ℝ)) ^ n)
      hsub (fun n _ _ => pow_nonneg (by positivity) _)
  calc
    _ = (1 - 1 / (p : ℝ)) * (1 + 1 / (p : ℝ)) := by rw [← one_div_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htwo (sub_nonneg.mpr (prime_reciprocal_lt_one hp).le)

private theorem one_sub_prime_inv_sq_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 - 1 / (p : ℝ) ^ 2 := by
  rw [← one_div_pow]
  exact sub_nonneg.mpr (by
    simpa using pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (p : ℝ))
      (prime_reciprocal_lt_one hp).le 2)

private theorem common_weight_lower {marker Y L : ℕ} {S : Finset ℕ}
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) (hL : 0 < L) :
    ((∏ o : Option ↥S, (1 - 1 / (exchangeAffected marker S o : ℝ))) * (1 / 2)) ≤
      digitRuleCommonWeight (exchangeAffected marker S) (Subtype.val :
        ↥(exchangeRough marker S Y) → ℕ) L := by
  let a := exchangeAffected marker S
  let R := exchangeRough marker S Y
  have ha (o : Option ↥S) : 0 ≤ 1 - 1 / (a o : ℝ) :=
    sub_nonneg.mpr (prime_reciprocal_lt_one (exchangeAffected_prime hm hS o)).le
  have hA : (∏ o, (1 - 1 / (a o : ℝ))) ≤ ∏ o, (1 - 1 / (a o : ℝ)) *
      ∑ h ∈ greedyExponentsBelow L, (1 / (a o : ℝ)) ^ (3 * h) := by
    refine Finset.prod_le_prod (fun o _ => ha o) fun o _ => ?_
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (high_weight_sum_ge_one (a o) L hL) (ha o)
  have hR₀ : (1 / 2 : ℝ) ≤ ∏ q : ↥R, (1 - 1 / (q.val : ℝ) ^ 2) := by
    rw [Finset.univ_eq_attach, Finset.prod_attach R (fun q : ℕ => 1 - 1 / (q : ℝ) ^ 2)]
    exact one_half_le_prod_one_sub_inv_sq R fun q hq => (exchangeRough_prime ⟨q, hq⟩).two_le
  have hR : (1 / 2 : ℝ) ≤ ∏ q : ↥R, (1 - 1 / (q.val : ℝ)) *
      ∑ n ∈ greedyExponentsBelow (3 * L), (1 / (q.val : ℝ)) ^ n :=
    hR₀.trans (Finset.prod_le_prod (fun q _ => one_sub_prime_inv_sq_nonneg (exchangeRough_prime q))
      (fun q _ => rough_factor_ge_one_sub_square q.val L (exchangeRough_prime q) hL))
  exact mul_le_mul hA hR (by norm_num) ((Finset.prod_nonneg fun o _ => ha o).trans hA)

/-- A strict finite cap-mass comparison gives a strict comparison of the
natural densities of the corresponding integer sets. -/
theorem naturalDensity_digitRuleSet_strict_mono_mass {marker : ℕ} {S : Finset ℕ}
    {C D : Set (ZMod 3 × (↥S → ZMod 3))} {dC dD : ℝ}
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) (hdisj : marker ∉ S)
    (hC : HasNaturalDensity (digitRuleSet marker S C) dC)
    (hD : HasNaturalDensity (digitRuleSet marker S D) dD)
    (hmass : digitCapMass (1 / (marker : ℝ)) (fun p : ↥S => 1 / (p.val : ℝ)) C <
      digitCapMass (1 / (marker : ℝ)) (fun p : ↥S => 1 / (p.val : ℝ)) D) : dC < dD := by
  let a := exchangeAffected marker S
  let mass (B : Set (ZMod 3 × (↥S → ZMod 3))) :=
    digitCapMass (1 / (marker : ℝ)) (fun p : ↥S => 1 / (p.val : ℝ)) B
  let base := (∏ o, (1 - 1 / (a o : ℝ))) * (1 / 2)
  let gap := mass D - mass C
  let δ := gap * base
  have hbase : 0 < base := mul_pos
    (Finset.prod_pos fun o _ => sub_pos.mpr (prime_reciprocal_lt_one (exchangeAffected_prime hm hS o)))
    (by norm_num)
  have hgap : 0 < gap := sub_pos.mpr hmass
  have hδ : 0 < δ := mul_pos hgap hbase
  obtain ⟨Y, L, hY, hL, hmY, hSY, hbound⟩ := exists_digitRule_cutoffs marker S
    (show 0 < δ / 4 by positivity)
  let r := (Subtype.val : ↥(exchangeRough marker S Y) → ℕ)
  let weight := digitRuleCommonWeight a r L
  have hclose (B : Set (ZMod 3 × (↥S → ZMod 3))) (d : ℝ)
      (hd : HasNaturalDensity (digitRuleSet marker S B) d) : |d - mass B * weight| ≤ δ / 4 := by
    have hf : HasNaturalDensity (finiteDigitRuleSet a r B L) (mass B * weight) :=
      hasNaturalDensity_finiteDigitRuleSet a r B L (exchangePrimeCoordinates_injective hdisj)
        (exchangeAffected_prime hm hS) exchangeRough_prime
    unfold HasNaturalDensity at hd hf
    exact le_of_tendsto' (hd.sub hf).abs fun N =>
      (abs_densityUpTo_digitRule_sub_trunc_le B N hm hS hmY hSY hY).trans hbound
  have hseparate : δ ≤ mass D * weight - mass C * weight := by
    calc
      δ ≤ gap * weight := mul_le_mul_of_nonneg_left (common_weight_lower hm hS hL) hgap.le
      _ = _ := sub_mul _ _ _
  linarith only [hδ, hseparate, (abs_le.mp (hclose C dC hC)).2, (abs_le.mp (hclose D dD hD)).1]

/-- Some one-digit exchange is free of rational-ratio three-term geometric
progressions and has strictly greater natural density than Rankin's set. -/
theorem exists_exchangedRankinSet_strictNaturalDensityGain :
    ∃ (S : Finset ℕ) (dR dE : ℝ), 2 ∉ S ∧ (∀ p ∈ S, p.Prime) ∧
      ThreeGPFree (exchangedRankinSet 2 S) ∧ HasNaturalDensity rankinSet dR ∧
      HasNaturalDensity (exchangedRankinSet 2 S) dE ∧ dR < dE := by
  obtain ⟨S, h₂, hS, hmass⟩ := exists_oneDigitExchange_mass_gain
  obtain ⟨dR, hR⟩ := exists_hasNaturalDensity_digitRuleSet (binaryDigitCap ↥S) Nat.prime_two hS h₂
  obtain ⟨dE, hE⟩ := exists_hasNaturalDensity_digitRuleSet (exchangedDigitCap ↥S)
    Nat.prime_two hS h₂
  exact ⟨S, dR, dE, h₂, hS, threeGPFree_exchangedRankinSet 2 S Nat.prime_two hS,
    (digitRuleSet_binary Nat.prime_two hS) ▸ hR, (digitRuleSet_exchanged 2 S) ▸ hE,
    naturalDensity_digitRuleSet_strict_mono_mass Nat.prime_two hS h₂ hR hE hmass⟩

end GRHArticle.ProgressionFree
