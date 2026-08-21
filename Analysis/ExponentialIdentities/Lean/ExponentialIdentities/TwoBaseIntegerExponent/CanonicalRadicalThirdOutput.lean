import ExponentialIdentities.TwoBaseIntegerExponent.RadicalDegree
import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveGenerator
import ExponentialIdentities.TwoBaseIntegerExponent.RationalThirdBase
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot

namespace LeanProofs.TwoBaseIntegerExponent

open Set Polynomial

noncomputable section

/-- For a reduced normalized radical, being an algebraic integer is equivalent to having
no power of three in the denominator of its first rational power. -/
theorem oddCoreRpow_isIntegral_iff_denominator_trivial
    {w d a c : ℕ} (hd : 0 < d)
    (hred : a = 0 ∨ ¬ 3 ∣ c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a) :
    IsIntegral ℤ (oddCoreRpow w) ↔ a = 0 := by
  constructor
  · intro hEint
    let q : ℚ := (c : ℚ) / (3 : ℚ) ^ a
    have hqCast : (q : ℝ) = oddCoreRpow w ^ d := by
      dsimp only [q]
      push_cast
      exact hnorm.symm
    have hqIntR : IsIntegral ℤ (q : ℝ) := by
      rw [hqCast]
      exact hEint.pow d
    have hqIntQ : IsIntegral ℤ q :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℝ)
        Rat.cast_injective).mp hqIntR
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqIntQ
    have hdenOne : q.den = 1 := by
      rw [← hz]
      exact Rat.den_intCast z
    have hdiv : 3 ^ a ∣ c := by
      apply (Rat.den_div_natCast_eq_one_iff c (3 ^ a)
        (pow_ne_zero _ (by norm_num : (3 : ℕ) ≠ 0))).mp
      simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using hdenOne
    by_contra ha
    have hc3 : ¬ 3 ∣ c := hred.resolve_left ha
    exact hc3 ((dvd_pow_self 3 ha).trans hdiv)
  · intro ha
    apply IsIntegral.of_pow hd
    rw [hnorm, ha]
    simpa using (isIntegral_natCast c : IsIntegral ℤ (c : ℝ))

/-- Raising the normalized rational power of the canonical radical to the solution
exponent is rational exactly when its reduced numerator has rational output. -/
theorem normalizedRadical_rpow_rational_iff_numerator_rpow_rational
    {w d a c : ℕ} {β : ℝ} (hc : 0 < c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (hthree : (3 : ℝ) ^ β = (c : ℝ)) :
    (∃ q : ℚ, (q : ℝ) = (oddCoreRpow w ^ d) ^ β) ↔
      ∃ q : ℚ, (q : ℝ) = (c : ℝ) ^ β := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hca : (0 : ℝ) < (c : ℝ) ^ a := pow_pos hcR _
  have hpow : (oddCoreRpow w ^ d) ^ β =
      (c : ℝ) ^ β / (c : ℝ) ^ a := by
    rw [hnorm, Real.div_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) β a, hthree]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q * (c ^ a : ℕ), ?_⟩
    push_cast
    rw [hq, hpow]
    field_simp
  · rintro ⟨q, hq⟩
    refine ⟨q / (c ^ a : ℕ), ?_⟩
    push_cast
    rw [hpow, hq]

/-- For a nonintegral two-base solution, the normalized radical's rational power has a
rational `β`-th output exactly when its numerator is `2,3`-smooth. -/
theorem normalizedRadical_rpow_rational_iff_numerator_threeSmooth
    {w d a c : ℕ} {β : ℝ} (hc : 0 < c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (hβ : TwoBaseNonintegerSolution β)
    (hthree : (3 : ℝ) ^ β = (c : ℝ)) :
    (∃ q : ℚ, (q : ℝ) = (oddCoreRpow w ^ d) ^ β) ↔
      ∃ u v : ℕ, c = 2 ^ u * 3 ^ v := by
  rw [normalizedRadical_rpow_rational_iff_numerator_rpow_rational
    hc hnorm hthree]
  exact hβ.rpow_rational_iff_eq_two_pow_mul_three_pow hc

/-- With a reduced nontrivial power-of-three denominator, rationality of the normalized
radical power's `β`-th output is equivalent to its numerator being a pure power of two. -/
theorem normalizedRadical_rpow_rational_iff_numerator_twoPow
    {w d a c : ℕ} {β : ℝ} (hc : 0 < c) (hc3 : ¬ 3 ∣ c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (hβ : TwoBaseNonintegerSolution β)
    (hthree : (3 : ℝ) ^ β = (c : ℝ)) :
    (∃ q : ℚ, (q : ℝ) = (oddCoreRpow w ^ d) ^ β) ↔
      ∃ u : ℕ, c = 2 ^ u := by
  rw [normalizedRadical_rpow_rational_iff_numerator_threeSmooth
    hc hnorm hβ hthree]
  constructor
  · rintro ⟨u, v, huv⟩
    have hv : v = 0 := by
      by_contra hv
      apply hc3
      rw [huv]
      exact (dvd_pow_self 3 hv).trans (dvd_mul_left _ _)
    exact ⟨u, by simpa [hv] using huv⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, 0, by simp⟩

/-- In the reduced-denominator case singled out above, the apparently merely rational
output is in fact the explicit natural number `w ^ (d * u)`. -/
theorem normalizedRadical_rpow_eq_core_pow_of_numerator_twoPow
    {w d a c u : ℕ} {β : ℝ}
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (htwo : (2 : ℝ) ^ β = ((2 ^ a * w ^ d : ℕ) : ℝ))
    (hthree : (3 : ℝ) ^ β = (c : ℝ))
    (hc : c = 2 ^ u) :
    (oddCoreRpow w ^ d) ^ β = ((w ^ (d * u) : ℕ) : ℝ) := by
  rw [hnorm, Real.div_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) β a, hthree]
  rw [hc]
  push_cast
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) β u, htwo]
  push_cast
  have hswap : ((2 : ℝ) ^ a) ^ u = ((2 : ℝ) ^ u) ^ a := by
    rw [← pow_mul, ← pow_mul, mul_comm a u]
  rw [mul_pow, hswap]
  field_simp
  rw [pow_mul]

/-- Exact reduced-denominator classification: a rational `β`-th output occurs precisely
when the numerator is a power of two, and then the output is the displayed natural core
power. -/
theorem normalizedRadical_rpow_rational_iff_exists_twoPow_and_eq_corePow
    {w d a c : ℕ} {β : ℝ} (hc : 0 < c) (hc3 : ¬ 3 ∣ c)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (hβ : TwoBaseNonintegerSolution β)
    (htwo : (2 : ℝ) ^ β = ((2 ^ a * w ^ d : ℕ) : ℝ))
    (hthree : (3 : ℝ) ^ β = (c : ℝ)) :
    (∃ q : ℚ, (q : ℝ) = (oddCoreRpow w ^ d) ^ β) ↔
      ∃ u : ℕ, c = 2 ^ u ∧
        (oddCoreRpow w ^ d) ^ β = ((w ^ (d * u) : ℕ) : ℝ) := by
  constructor
  · intro hrat
    obtain ⟨u, hu⟩ :=
      (normalizedRadical_rpow_rational_iff_numerator_twoPow
        hc hc3 hnorm hβ hthree).mp hrat
    exact ⟨u, hu,
      normalizedRadical_rpow_eq_core_pow_of_numerator_twoPow
        hnorm htwo hthree hu⟩
  · rintro ⟨u, _hu, hout⟩
    exact ⟨(w ^ (d * u) : ℕ), by exact_mod_cast hout.symm⟩

/-- Failure produces one canonical radical field for which the exact degree and the full
rational-output restriction above hold simultaneously.  In particular, when its reduced
denominator is nontrivial, any rational `β`-th power of the normalized radical power is
automatically the explicit integer `w ^ (d * u)`. -/
theorem exists_exact_radical_degree_and_thirdOutput_constraint
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ w d a c : ℕ, ∃ β : ℝ,
      Odd w ∧ 1 < w ∧ 0 < d ∧ 0 < c ∧
      (a = 0 ∨ ¬ 3 ∣ c) ∧
      oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a ∧
      Irreducible (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a)) ∧
      minpoly ℚ (oddCoreRpow w) =
        X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a) ∧
      (minpoly ℚ (oddCoreRpow w)).natDegree = d ∧
      (IsIntegral ℤ (oddCoreRpow w) ↔ a = 0) ∧
      IsLeastTwoBaseNonintegerSolution β ∧
      (2 : ℝ) ^ β = ((2 ^ a * w ^ d : ℕ) : ℝ) ∧
      (3 : ℝ) ^ β = (c : ℝ) ∧
      ((∃ q : ℚ, (q : ℝ) = (oddCoreRpow w ^ d) ^ β) ↔
        ∃ u v : ℕ, c = 2 ^ u * 3 ^ v) ∧
      (0 < a →
        ((∃ q : ℚ, (q : ℝ) = (oddCoreRpow w ^ d) ^ β) ↔
          ∃ u : ℕ, c = 2 ^ u ∧
            (oddCoreRpow w ^ d) ^ β = ((w ^ (d * u) : ℕ) : ℝ))) := by
  obtain ⟨w, d, a, c, β, hwodd, hw, _hwgcd, hd, hc, ha,
      _hindex, hleast, hnorm, _hβdef, htwo, hthree, _hβirr,
      hβleast, _hchar, _hcand⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  obtain ⟨hirr, hmin, hdeg⟩ :=
    oddCoreRpow_exact_radical_degree (by omega) hd hleast hnorm
  have hint : IsIntegral ℤ (oddCoreRpow w) ↔ a = 0 :=
    oddCoreRpow_isIntegral_iff_denominator_trivial hd ha hnorm
  refine ⟨w, d, a, c, β, hwodd, hw, hd, hc, ha, hnorm,
    hirr, hmin, hdeg, hint, hβleast, htwo, hthree, ?_, ?_⟩
  · exact normalizedRadical_rpow_rational_iff_numerator_threeSmooth
      hc hnorm hβleast.1 hthree
  · intro haPos
    have hc3 : ¬ 3 ∣ c := ha.resolve_left haPos.ne'
    exact normalizedRadical_rpow_rational_iff_exists_twoPow_and_eq_corePow
      hc hc3 hnorm hβleast.1 htwo hthree

end

end LeanProofs.TwoBaseIntegerExponent
