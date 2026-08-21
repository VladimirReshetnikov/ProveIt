import ExponentialIdentities.TwoBaseIntegerExponent.RadicalDegree
import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveOddCore
import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveGenerator

namespace LeanProofs.TwoBaseIntegerExponent

open Set Finset Polynomial

noncomputable section

private theorem exists_pow_eq_of_dvd_factorization {c k : ℕ}
    (hc0 : c ≠ 0) (hdiv : ∀ p : ℕ, k ∣ c.factorization p) :
    ∃ r : ℕ, c = r ^ k := by
  let factors := c.factorization.mapRange (fun e : ℕ ↦ e / k) (Nat.zero_div k)
  set r := factors.prod (· ^ ·) with hr
  refine ⟨r, ?_⟩
  apply Nat.eq_of_factorization_eq hc0 (by simp [r, factors])
  intro p
  have hprime (q : ℕ) (hq : q ∈ factors.support) : q.Prime :=
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hq)
  rw [Nat.factorization_pow, hr, Nat.prod_pow_factorization_eq_self hprime]
  simp [factors, Nat.mul_div_cancel' (hdiv p)]

/-- A divisor of the valuation gcd is an honest outer power exponent, including the
empty-support case `c = 1`, where the valuation gcd is zero. -/
theorem exists_pow_eq_of_dvd_oddPrimeValuationGCD
    {c k : ℕ} (hc : 0 < c) (hk : k ∣ oddPrimeValuationGCD c) :
    ∃ r : ℕ, c = r ^ k := by
  apply exists_pow_eq_of_dvd_factorization hc.ne'
  intro p
  by_cases hp : p ∈ c.primeFactors
  · exact hk.trans (Finset.gcd_dvd hp)
  · have hz : c.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa using hp)
    simp [hz]

/-- If `d` is the least positive exponent making `E ^ d` rational and
`E ^ d = c / 3 ^ a`, then `d`, the denominator exponent, and the gcd of the numerator's
prime valuations have no common factor. -/
theorem rationalPowerIndex_gcd_denominator_valuationGCD_eq_one
    {E : ℝ} (hE : 0 < E) {d a c : ℕ} (hd : 0 < d) (hc : 0 < c)
    (hnorm : E ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (hleast : ∀ n : ℕ, E ^ n ∈ Set.range ((↑) : ℚ → ℝ) →
      0 < n → d ≤ n) :
    Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) = 1 := by
  let g := Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c))
  have hgd : g ∣ d := Nat.gcd_dvd_left _ _
  have hga : g ∣ a :=
    (Nat.gcd_dvd_right d (Nat.gcd a (oddPrimeValuationGCD c))).trans
      (Nat.gcd_dvd_left a (oddPrimeValuationGCD c))
  have hgc : g ∣ oddPrimeValuationGCD c :=
    (Nat.gcd_dvd_right d (Nat.gcd a (oddPrimeValuationGCD c))).trans
      (Nat.gcd_dvd_right a (oddPrimeValuationGCD c))
  have hgpos : 0 < g := by
    have : g ≠ 0 := by
      intro hg
      have : d = 0 := Nat.eq_zero_of_zero_dvd (hg ▸ hgd)
      omega
    omega
  by_contra hg1
  have hg2 : 2 ≤ g := by omega
  obtain ⟨d₀, hd₀⟩ := hgd
  obtain ⟨a₀, ha₀⟩ := hga
  obtain ⟨r, hcr⟩ := exists_pow_eq_of_dvd_oddPrimeValuationGCD hc hgc
  have hd₀pos : 0 < d₀ := by
    by_contra hnpos
    have hd₀zero : d₀ = 0 := Nat.eq_zero_of_not_pos hnpos
    rw [hd₀zero, mul_zero] at hd₀
    omega
  have hpow : (E ^ d₀) ^ g =
      ((r : ℝ) / (3 : ℝ) ^ a₀) ^ g := by
    rw [← pow_mul]
    rw [mul_comm d₀ g, ← hd₀, hnorm]
    rw [hcr, ha₀]
    push_cast
    rw [div_pow, mul_comm g a₀, pow_mul]
  have hroot : E ^ d₀ = (r : ℝ) / (3 : ℝ) ^ a₀ := by
    apply (pow_left_inj₀ (pow_nonneg hE.le _)
      (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)) hgpos.ne').mp
    exact hpow
  have hrat : E ^ d₀ ∈ Set.range ((↑) : ℚ → ℝ) := by
    refine ⟨(r : ℚ) / (3 : ℚ) ^ a₀, ?_⟩
    push_cast
    exact hroot.symm
  have hle : d ≤ d₀ := hleast d₀ hrat hd₀pos
  rw [hd₀] at hle
  nlinarith

/-- Primewise form of the valuation restriction: a prime factor of both the least
rational-power index and the denominator exponent must fail to divide at least one
positive numerator valuation. This also covers `c = 1`: in that case the hypotheses
on `p` are contradictory, since the requested witness set is empty. -/
theorem exists_primeValuation_not_dvd_of_prime_dvd_rationalPowerIndex
    {E : ℝ} (hE : 0 < E) {d a c p : ℕ} (hd : 0 < d) (hc : 0 < c)
    (hnorm : E ^ d = (c : ℝ) / (3 : ℝ) ^ a)
    (hleast : ∀ n : ℕ, E ^ n ∈ Set.range ((↑) : ℚ → ℝ) →
      0 < n → d ≤ n)
    (hp : p.Prime) (hpd : p ∣ d) (hpa : p ∣ a) :
    ∃ ℓ ∈ c.primeFactors, ¬ p ∣ c.factorization ℓ := by
  have hgcd := rationalPowerIndex_gcd_denominator_valuationGCD_eq_one
    hE hd hc hnorm hleast
  by_contra h
  push Not at h
  have hpval : p ∣ oddPrimeValuationGCD c := by
    apply Finset.dvd_gcd
    intro ℓ hℓ
    exact h ℓ hℓ
  have hpinner : p ∣ Nat.gcd a (oddPrimeValuationGCD c) := Nat.dvd_gcd hpa hpval
  have hpouter : p ∣ Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) :=
    Nat.dvd_gcd hpd hpinner
  rw [hgcd] at hpouter
  exact hp.not_dvd_one hpouter

/-- Failure produces a canonical primitive radical whose exact degree and normalized
rational power satisfy the simultaneous denominator/numerator valuation obstruction. -/
theorem exists_exact_radical_degree_and_valuation_restriction
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ w d a c : ℕ,
      Odd w ∧ 1 < w ∧ oddPrimeValuationGCD w = 1 ∧
      0 < d ∧ 0 < c ∧ (a = 0 ∨ ¬ 3 ∣ c) ∧
      oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a ∧
      Irreducible (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a)) ∧
      minpoly ℚ (oddCoreRpow w) =
        X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a) ∧
      (minpoly ℚ (oddCoreRpow w)).natDegree = d ∧
      Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) = 1 ∧
      ∀ p : ℕ, p.Prime → p ∣ d → p ∣ a →
        ∃ ℓ ∈ c.primeFactors, ¬ p ∣ c.factorization ℓ := by
  obtain ⟨w, d, a, c, _β, hwodd, hw, hwgcd, hd, hc, ha,
      _hindex, hleast, hnorm, _hβdef, _htwo, _hthree, _hβirr,
      _hβleast, _hchar, _hcand⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  obtain ⟨hirr, hmin, hdeg⟩ :=
    oddCoreRpow_exact_radical_degree (by omega) hd hleast hnorm
  have hleastNat : ∀ n : ℕ,
      oddCoreRpow w ^ n ∈ Set.range ((↑) : ℚ → ℝ) →
      0 < n → d ≤ n := by
    intro n hnRat hn
    have hnRatZ : oddCoreRpow w ^ (n : ℤ) ∈
        Set.range ((↑) : ℚ → ℝ) := by
      simpa using hnRat
    have hdnZ := hleast (n : ℤ) hnRatZ (by exact_mod_cast hn)
    exact_mod_cast hdnZ
  have hgcd : Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) = 1 :=
    rationalPowerIndex_gcd_denominator_valuationGCD_eq_one
      (oddCoreRpow_pos (by omega)) hd hc hnorm hleastNat
  refine ⟨w, d, a, c, hwodd, hw, hwgcd, hd, hc, ha, hnorm,
    hirr, hmin, hdeg, hgcd, ?_⟩
  intro p hp hpd hpa
  exact exists_primeValuation_not_dvd_of_prime_dvd_rationalPowerIndex
    (oddCoreRpow_pos (by omega)) hd hc hnorm hleastNat hp hpd hpa

end

end LeanProofs.TwoBaseIntegerExponent
