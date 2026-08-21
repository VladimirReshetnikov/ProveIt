import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveOddCore
import ExponentialIdentities.TwoBaseIntegerExponent.RationalPowerIndex

/-!
# The exact primitive generator of all hypothetical solutions

This module combines the canonical primitive odd core with the rational-power index and its
power-of-three denominator normalization.  Conditional on failure of the Alaoglu--Erdős
conjecture, it upgrades the earlier rank-two containment to an exact free additive monoid:

`x` is a solution if and only if `x = n + k * β` for unique `n k : ℕ`,

where `β = a + d * logb 2 w` is irrational and is the least noninteger solution.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- **Canonical primitive-generator theorem.**  If the Alaoglu--Erdős conjecture fails,
there are a canonical gcd-normalized odd core `w`, a least rational-power index `d`, and a
reduced power-of-three denominator `3 ^ a`.  The resulting irrational `β` is the least
noninteger solution, and every solution has unique coordinates `n + k * β`. -/
theorem exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ w d a c : ℕ, ∃ β : ℝ,
      Odd w ∧ 1 < w ∧ oddPrimeValuationGCD w = 1 ∧
      0 < d ∧ 0 < c ∧ (a = 0 ∨ ¬ 3 ∣ c) ∧
      (∀ j : ℤ, oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) ↔ (d : ℤ) ∣ j) ∧
      (∀ j : ℤ, oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) →
        0 < j → (d : ℤ) ≤ j) ∧
      oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a ∧
      β = (a : ℝ) + d * Real.logb 2 w ∧
      (2 : ℝ) ^ β = ((2 ^ a * w ^ d : ℕ) : ℝ) ∧
      (3 : ℝ) ^ β = (c : ℝ) ∧
      Irrational β ∧ IsLeastTwoBaseNonintegerSolution β ∧
      (∀ x : ℝ, TwoBaseIntegralSolution x ↔
        ∃! nk : ℕ × ℕ, x = (nk.1 : ℝ) + (nk.2 : ℝ) * β) ∧
      ∀ m : ℕ, TwoBaseNaturalCandidate m ↔
        ∃! nk : ℕ × ℕ,
          m = 2 ^ nk.1 * (2 ^ a * w ^ d) ^ nk.2 := by
  classical
  have hcounter : ∃ m : ℕ, TwoBaseNaturalCandidate m ∧
      ¬ ∃ n : ℕ, m = 2 ^ n := by
    rw [alaogluErdosConjecture_iff_candidates_are_powers_of_two] at hfail
    push Not at hfail
    simpa only [not_exists] using hfail
  obtain ⟨w, hw, _hwunique⟩ := existsUnique_primitive_common_odd_core hcounter
  have hrep : ∀ m : ℕ, TwoBaseNaturalCandidate m →
      ∃ i j : ℕ, m = 2 ^ i * w ^ j := by
    intro m hm
    obtain ⟨ij, hij, _hijUnique⟩ := hw.2.2.2 m hm
    exact ⟨ij.1, ij.2, hij⟩
  obtain ⟨d, a, c, hd, hc, ha, hindex, hleastIndex, hnorm, hchar, hβleast⟩ :=
    exists_exact_solution_monoid_of_fixed_common_oddCore
      hw.1 hw.2.1 hrep hcounter
  let β : ℝ := (a : ℝ) + d * Real.logb 2 w
  have hβirr : Irrational β :=
    irrational_of_not_integer_of_two_rpow_integer hβleast.1.2 hβleast.1.1.1
  have hM : TwoBaseNaturalCandidate (2 ^ a * w ^ d) := by
    simpa using
      (twoBaseNaturalCandidate_primitive_coordinates_iff (w := w) (d := d)
        (a := a) (c := c) (i := a) (k := 1) (by omega) hc ha hnorm).mpr (by simp)
  have hMexp : twoBaseCandidateExponent (2 ^ a * w ^ d) = β := by
    rw [twoBaseCandidateExponent_eq_add_mul_logb_of_oddCore_rep (by omega) rfl]
  have h₂β : (2 : ℝ) ^ β = ((2 ^ a * w ^ d : ℕ) : ℝ) := by
    rw [← hMexp, two_rpow_twoBaseCandidateExponent hM.1]
  have h₃β : (3 : ℝ) ^ β = (c : ℝ) := by
    calc
      (3 : ℝ) ^ β = (3 : ℝ) ^ twoBaseCandidateExponent (2 ^ a * w ^ d) := by
        rw [hMexp]
      _ = ((2 ^ a * w ^ d : ℕ) : ℝ) ^ logThreeDivLogTwo :=
        three_rpow_twoBaseCandidateExponent hM.1
      _ = (3 : ℝ) ^ a * oddCoreRpow w ^ d :=
        candidateRpow_eq_three_pow_mul_oddCoreRpow_pow rfl
      _ = (c : ℝ) := by rw [hnorm]; field_simp
  have hinj : Function.Injective
      (fun nk : ℕ × ℕ ↦ (nk.1 : ℝ) + (nk.2 : ℝ) * β) :=
    IntegerExponent.Irrational.injective_nat_add_mul hβirr
  have hsolUnique : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃! nk : ℕ × ℕ, x = (nk.1 : ℝ) + (nk.2 : ℝ) * β := by
    intro x
    constructor
    · intro hx
      obtain ⟨n, k, hxrep⟩ := (hchar x).mp hx
      refine ⟨(n, k), by simpa only [β] using hxrep, ?_⟩
      intro nk hnk
      apply hinj
      exact hnk.symm.trans (by simpa only [β] using hxrep)
    · rintro ⟨nk, hnk, _⟩
      apply (hchar x).mpr
      exact ⟨nk.1, nk.2, by simpa only [β] using hnk⟩
  have hpowCoord (nk : ℕ × ℕ) :
      (2 : ℝ) ^ ((nk.1 : ℝ) + (nk.2 : ℝ) * β) =
        ((2 ^ nk.1 * (2 ^ a * w ^ d) ^ nk.2 : ℕ) : ℝ) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
    rw [mul_comm (nk.2 : ℝ) β,
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), h₂β]
    push_cast
    rfl
  have hcandUnique : ∀ m : ℕ, TwoBaseNaturalCandidate m ↔
      ∃! nk : ℕ × ℕ, m = 2 ^ nk.1 * (2 ^ a * w ^ d) ^ nk.2 := by
    intro m
    constructor
    · intro hm
      obtain ⟨nk, hxrep, hxunique⟩ := (hsolUnique (twoBaseCandidateExponent m)).mp
        hm.integer_powers
      refine ⟨nk, ?_, ?_⟩
      · have hcast : (m : ℝ) =
            ((2 ^ nk.1 * (2 ^ a * w ^ d) ^ nk.2 : ℕ) : ℝ) := by
          calc
            (m : ℝ) = (2 : ℝ) ^ twoBaseCandidateExponent m :=
              (two_rpow_twoBaseCandidateExponent hm.1).symm
            _ = (2 : ℝ) ^ ((nk.1 : ℝ) + (nk.2 : ℝ) * β) := by rw [hxrep]
            _ = ((2 ^ nk.1 * (2 ^ a * w ^ d) ^ nk.2 : ℕ) : ℝ) := hpowCoord nk
        exact_mod_cast hcast
      · intro nk' hnk'
        apply hxunique nk'
        apply (Real.strictMono_rpow_of_base_gt_one
          (by norm_num : (1 : ℝ) < 2)).injective
        calc
          (2 : ℝ) ^ twoBaseCandidateExponent m = (m : ℝ) :=
            two_rpow_twoBaseCandidateExponent hm.1
          _ = ((2 ^ nk'.1 * (2 ^ a * w ^ d) ^ nk'.2 : ℕ) : ℝ) := by
            exact_mod_cast hnk'
          _ = (2 : ℝ) ^ ((nk'.1 : ℝ) + (nk'.2 : ℝ) * β) :=
            (hpowCoord nk').symm
    · rintro ⟨nk, rfl, _⟩
      have hcoord : TwoBaseNaturalCandidate
          (2 ^ (nk.1 + a * nk.2) * w ^ (d * nk.2)) :=
        (twoBaseNaturalCandidate_primitive_coordinates_iff
          (w := w) (d := d) (a := a) (c := c)
          (i := nk.1 + a * nk.2) (k := nk.2)
          (by omega) hc ha hnorm).mpr (Nat.le_add_left _ _)
      have heq :
          2 ^ nk.1 * (2 ^ a * w ^ d) ^ nk.2 =
            2 ^ (nk.1 + a * nk.2) * w ^ (d * nk.2) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        rw [← mul_assoc, ← pow_add]
      rwa [heq]
  exact ⟨w, d, a, c, β, hw.1, hw.2.1, hw.2.2.1, hd, hc, ha,
    hindex, hleastIndex, hnorm, rfl,
    h₂β, h₃β, hβirr, hβleast, hsolUnique, hcandUnique⟩

end

end LeanProofs.TwoBaseIntegerExponent
