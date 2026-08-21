import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicRationalBase
import ExponentialIdentities.TwoBaseIntegerExponent.CanonicalRadicalThirdOutput

/-!
# Algebraic output of the canonical radical

This module upgrades the rational-output restriction for the normalized canonical
radical to its own `β`-th power. Algebraicity is equivalent to smoothness of the
normalized numerator; with a nontrivial reduced denominator, the output is exactly
an explicit natural core power.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set Polynomial

noncomputable section

/-- Algebraicity of the canonical radical's `β`-th power is controlled exactly by
the `2,3`-smoothness of the numerator of its first rational power. -/
theorem oddCoreRpow_rpow_isAlgebraic_iff_numerator_threeSmooth
    {w d a c : ℕ} {β : ℝ} (hw : 0 < w) (hd : 0 < d) (hc : 0 < c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (hβ : TwoBaseNonintegerSolution β)
    (hthree : (3 : ℝ) ^ β = (c : ℝ)) :
    IsAlgebraic ℚ ((oddCoreRpow w) ^ β) ↔
      ∃ u v : ℕ, c = 2 ^ u * 3 ^ v := by
  let q : ℚ := (c : ℚ) / (3 : ℚ) ^ a
  have hqpos : 0 < q := by
    dsimp only [q]
    positivity
  have hqcast : (q : ℝ) = oddCoreRpow w ^ d := by
    dsimp only [q]
    push_cast
    exact hnorm.symm
  constructor
  · intro hAlg
    have hAlgPow : IsAlgebraic ℚ ((oddCoreRpow w ^ d) ^ β) := by
      rw [← Real.rpow_pow_comm (oddCoreRpow_pos hw).le β d]
      exact hAlg.pow d
    have hAlgQ : IsAlgebraic ℚ ((q : ℝ) ^ β) := by
      rw [hqcast]
      exact hAlgPow
    have hunit : IsTwoThreeUnit q :=
      (twoBaseNonintegerSolution_rat_rpow_isAlgebraic_iff_isTwoThreeUnit
        hβ hqpos).mp hAlgQ
    obtain ⟨r, hr⟩ :=
      (rat_rpow_rational_iff_isTwoThreeUnit_of_not_integer
        hβ.2 hβ.1.1 hβ.1.2 hqpos).mpr hunit
    have hrat : ∃ r : ℚ, (r : ℝ) = (oddCoreRpow w ^ d) ^ β := by
      exact ⟨r, by simpa only [hqcast] using hr⟩
    exact (normalizedRadical_rpow_rational_iff_numerator_threeSmooth
      hc hnorm hβ hthree).mp hrat
  · intro hsmooth
    obtain ⟨r, hr⟩ :=
      (normalizedRadical_rpow_rational_iff_numerator_threeSmooth
        hc hnorm hβ hthree).mpr hsmooth
    have hAlgPow : IsAlgebraic ℚ (((oddCoreRpow w) ^ β) ^ d) := by
      rw [Real.rpow_pow_comm (oddCoreRpow_pos hw).le β d]
      rw [← hr]
      exact isAlgebraic_algebraMap r
    exact IsAlgebraic.of_pow hd hAlgPow

/-- With a reduced nontrivial power-of-three denominator, the radical itself has
algebraic `β`-th power exactly when the numerator is a pure power of two; in that
case its output is the explicit natural number `w ^ u`. -/
theorem oddCoreRpow_rpow_isAlgebraic_iff_exists_twoPow_and_eq_corePow
    {w d a c : ℕ} {β : ℝ} (hw : 0 < w) (hd : 0 < d) (hc : 0 < c)
    (hc3 : ¬ 3 ∣ c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (hβ : TwoBaseNonintegerSolution β)
    (htwo : (2 : ℝ) ^ β = ((2 ^ a * w ^ d : ℕ) : ℝ))
    (hthree : (3 : ℝ) ^ β = (c : ℝ)) :
    IsAlgebraic ℚ ((oddCoreRpow w) ^ β) ↔
      ∃ u : ℕ, c = 2 ^ u ∧
        (oddCoreRpow w) ^ β = ((w ^ u : ℕ) : ℝ) := by
  constructor
  · intro hAlg
    obtain ⟨u, v, huv⟩ :=
      (oddCoreRpow_rpow_isAlgebraic_iff_numerator_threeSmooth
        hw hd hc hnorm hβ hthree).mp hAlg
    have hv : v = 0 := by
      by_contra hv0
      apply hc3
      rw [huv]
      exact (dvd_pow_self 3 hv0).trans (dvd_mul_left _ _)
    have hcu : c = 2 ^ u := by simpa [hv] using huv
    have hout := normalizedRadical_rpow_eq_core_pow_of_numerator_twoPow
      hnorm htwo hthree hcu
    have heqpow : ((oddCoreRpow w) ^ β) ^ d = (((w ^ u : ℕ) : ℝ)) ^ d := by
      calc
        ((oddCoreRpow w) ^ β) ^ d = (oddCoreRpow w ^ d) ^ β :=
          Real.rpow_pow_comm (oddCoreRpow_pos hw).le β d
        _ = ((w ^ (d * u) : ℕ) : ℝ) := hout
        _ = (((w ^ u : ℕ) : ℝ)) ^ d := by
          push_cast
          rw [← pow_mul, mul_comm d u]
    have heq : (oddCoreRpow w) ^ β = ((w ^ u : ℕ) : ℝ) :=
      (pow_left_inj₀
        (Real.rpow_pos_of_pos (oddCoreRpow_pos hw) β).le
        (by positivity) hd.ne').mp heqpow
    exact ⟨u, hcu, heq⟩
  · rintro ⟨u, _hcu, hout⟩
    rw [hout]
    exact isAlgebraic_nat (w ^ u)

/-- Failure produces a canonical radical for which algebraicity of the radical's own
`β`-th power has the exact smooth-numerator classification. If the reduced denominator
is nontrivial, an algebraic output is necessarily the explicit integer `w ^ u`. -/
theorem exists_canonical_radical_rpow_algebraic_constraint
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ w d a c : ℕ, ∃ β : ℝ,
      Odd w ∧ 1 < w ∧ 0 < d ∧ 0 < c ∧
      (a = 0 ∨ ¬ 3 ∣ c) ∧
      oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a ∧
      IsLeastTwoBaseNonintegerSolution β ∧
      (2 : ℝ) ^ β = ((2 ^ a * w ^ d : ℕ) : ℝ) ∧
      (3 : ℝ) ^ β = (c : ℝ) ∧
      (IsAlgebraic ℚ ((oddCoreRpow w) ^ β) ↔
        ∃ u v : ℕ, c = 2 ^ u * 3 ^ v) ∧
      (0 < a →
        (IsAlgebraic ℚ ((oddCoreRpow w) ^ β) ↔
          ∃ u : ℕ, c = 2 ^ u ∧
            (oddCoreRpow w) ^ β = ((w ^ u : ℕ) : ℝ))) := by
  obtain ⟨w, d, a, c, β, hwodd, hw, _hwgcd, hd, hc, ha,
      _hindex, _hleast, hnorm, _hβdef, htwo, hthree, _hβirr,
      hβleast, _hchar, _hcand⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  refine ⟨w, d, a, c, β, hwodd, hw, hd, hc, ha, hnorm,
    hβleast, htwo, hthree, ?_, ?_⟩
  · exact oddCoreRpow_rpow_isAlgebraic_iff_numerator_threeSmooth
      (by omega) hd hc hnorm hβleast.1 hthree
  · intro haPos
    have hc3 : ¬ 3 ∣ c := ha.resolve_left haPos.ne'
    exact oddCoreRpow_rpow_isAlgebraic_iff_exists_twoPow_and_eq_corePow
      (by omega) hd hc hc3 hnorm hβleast.1 htwo hthree

end

end LeanProofs.TwoBaseIntegerExponent
