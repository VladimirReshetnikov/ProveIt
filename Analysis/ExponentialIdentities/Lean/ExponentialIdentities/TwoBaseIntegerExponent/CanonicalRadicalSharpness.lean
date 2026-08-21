import ExponentialIdentities.TwoBaseIntegerExponent.CanonicalRadicalValuation
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Data.Rat.Lemmas

/-!
# Sharp arithmetic of the canonical radical normalization

For a reduced positive rational `c / 3 ^ a`, this module identifies exactly when it is a
rational outer power. In odd degree this makes the triple-gcd restriction from
`CanonicalRadicalValuation` equivalent to irreducibility of the normalized binomial.

The triple gcd cannot be replaced by either pairwise gcd. For example,
`X ^ 3 - 2 / 27` is irreducible although `gcd 3 3 = 3`, while `X ^ 3 - 8 / 3` is
irreducible although the numerator valuation gcd is `3`. In each case the remaining
coordinate makes the triple gcd equal to one.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set Finset Polynomial IntermediateField

noncomputable section

private theorem coprime_three_pow_of_reduced {a c : ℕ}
    (hred : a = 0 ∨ ¬ 3 ∣ c) : Nat.Coprime c (3 ^ a) := by
  rcases a.eq_zero_or_pos with rfl | ha
  · simp
  · apply Nat.Coprime.pow_right
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr
      (hred.resolve_left ha.ne')).symm

/-- In reduced `c / 3 ^ a` form, being a rational `p`-th power forces `p` to
divide the denominator exponent and every positive numerator valuation. -/
theorem dvd_denominator_and_valuations_of_rat_pow_eq_reduced
    {a c p : ℕ} (hred : a = 0 ∨ ¬ 3 ∣ c)
    {b : ℚ} (hb : b ^ p = (c : ℚ) / (3 : ℚ) ^ a) :
    p ∣ a ∧ ∀ ℓ ∈ c.primeFactors, p ∣ c.factorization ℓ := by
  have hcop : Nat.Coprime c (3 ^ a) := coprime_three_pow_of_reduced hred
  have hdenTarget : ((c : ℚ) / (3 : ℚ) ^ a).den = 3 ^ a := by
    have h := Rat.den_div_eq_of_coprime
      (a := (c : ℤ)) (b := (3 ^ a : ℕ)) (by positivity) (by simpa using hcop)
    norm_num at h ⊢
    exact_mod_cast h
  have hnumTarget : ((c : ℚ) / (3 : ℚ) ^ a).num = (c : ℤ) := by
    have h := Rat.num_div_eq_of_coprime
      (a := (c : ℤ)) (b := (3 ^ a : ℕ)) (by positivity) (by simpa using hcop)
    norm_num at h ⊢
    exact h
  have hden : b.den ^ p = 3 ^ a := by
    rw [← Rat.den_pow, hb, hdenTarget]
  have hnum : b.num ^ p = (c : ℤ) := by
    rw [← Rat.num_pow, hb, hnumTarget]
  have hdenVal := DFunLike.congr_fun
    (congrArg Nat.factorization hden) 3
  have hp3 : Nat.Prime 3 := by norm_num
  simp only [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    hp3.factorization, Finsupp.single_eq_same] at hdenVal
  have hpa : p ∣ a := by
    refine ⟨b.den.factorization 3, ?_⟩
    have hcast : a * 1 = p * b.den.factorization 3 := by
      exact_mod_cast hdenVal.symm
    simpa using hcast
  refine ⟨hpa, ?_⟩
  intro ℓ hℓ
  have hnumAbs := congrArg Int.natAbs hnum
  simp only [Int.natAbs_pow, Int.natAbs_natCast] at hnumAbs
  have hval := DFunLike.congr_fun
    (congrArg Nat.factorization hnumAbs) ℓ
  simp only [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul] at hval
  exact ⟨b.num.natAbs.factorization ℓ, hval.symm⟩

/-- Exact arithmetic characterization of rational outer powers in reduced normalized
form. It includes the empty-support case `c = 1`. -/
theorem exists_rat_pow_eq_reduced_iff_dvd_denominator_and_valuationGCD
    {a c p : ℕ} (hc : 0 < c) (hred : a = 0 ∨ ¬ 3 ∣ c) :
    (∃ b : ℚ, b ^ p = (c : ℚ) / (3 : ℚ) ^ a) ↔
      p ∣ a ∧ p ∣ oddPrimeValuationGCD c := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hpa, hpvals⟩ :=
      dvd_denominator_and_valuations_of_rat_pow_eq_reduced hred hb
    refine ⟨hpa, ?_⟩
    apply Finset.dvd_gcd
    intro ℓ hℓ
    exact hpvals ℓ hℓ
  · rintro ⟨hpa, hpvg⟩
    obtain ⟨a₀, ha₀⟩ := hpa
    obtain ⟨r, hcr⟩ := exists_pow_eq_of_dvd_oddPrimeValuationGCD hc hpvg
    refine ⟨(r : ℚ) / (3 : ℚ) ^ a₀, ?_⟩
    rw [div_pow, hcr, ha₀]
    push_cast
    rw [mul_comm p a₀, pow_mul]

/-- For odd degree, the valuation gcd condition is sufficient for irreducibility of the
reduced positive binomial. Thus the obstruction obtained from leastness is sharp in odd
degree, rather than merely a necessary consequence. -/
theorem irreducible_normalized_binomial_of_odd_of_valuationGCD_eq_one
    {d a c : ℕ} (hdodd : Odd d) (hred : a = 0 ∨ ¬ 3 ∣ c)
    (hgcd : Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) = 1) :
    Irreducible
      (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a)) := by
  apply (X_pow_sub_C_irreducible_iff_forall_prime_of_odd hdodd).mpr
  intro p hp hpd b hb
  obtain ⟨hpa, hpvals⟩ :=
    dvd_denominator_and_valuations_of_rat_pow_eq_reduced hred hb
  have hpvg : p ∣ oddPrimeValuationGCD c := by
    apply Finset.dvd_gcd
    intro ℓ hℓ
    exact hpvals ℓ hℓ
  have hpinner : p ∣ Nat.gcd a (oddPrimeValuationGCD c) :=
    Nat.dvd_gcd hpa hpvg
  have hpouter : p ∣ Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) :=
    Nat.dvd_gcd hpd hpinner
  rw [hgcd] at hpouter
  exact hp.not_dvd_one hpouter

/-- Irreducibility of a normalized binomial forces the triple valuation gcd condition.
This direction does not require odd degree or reducedness. -/
theorem valuationGCD_eq_one_of_irreducible_normalized_binomial
    {d a c : ℕ} (hd : 0 < d) (hc : 0 < c)
    (hirr : Irreducible
      (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a))) :
    Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) = 1 := by
  let g := Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c))
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  by_contra hg1
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
  have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpa : p ∣ a := hpg.trans
    ((Nat.gcd_dvd_right d (Nat.gcd a (oddPrimeValuationGCD c))).trans
      (Nat.gcd_dvd_left a (oddPrimeValuationGCD c)))
  have hpvg : p ∣ oddPrimeValuationGCD c := hpg.trans
    ((Nat.gcd_dvd_right d (Nat.gcd a (oddPrimeValuationGCD c))).trans
      (Nat.gcd_dvd_right a (oddPrimeValuationGCD c)))
  obtain ⟨a₀, ha₀⟩ := hpa
  obtain ⟨r, hcr⟩ := exists_pow_eq_of_dvd_oddPrimeValuationGCD hc hpvg
  have hpow : ((r : ℚ) / (3 : ℚ) ^ a₀) ^ p =
      (c : ℚ) / (3 : ℚ) ^ a := by
    rw [div_pow, hcr, ha₀]
    push_cast
    rw [mul_comm p a₀, pow_mul]
  exact (pow_ne_of_irreducible_X_pow_sub_C hirr hpd hp.ne_one
    ((r : ℚ) / (3 : ℚ) ^ a₀)) hpow

/-- For reduced positive binomials of odd degree, the triple valuation gcd is exactly
the irreducibility criterion. -/
theorem irreducible_normalized_binomial_iff_valuationGCD_eq_one_of_odd
    {d a c : ℕ} (hdodd : Odd d) (hc : 0 < c)
    (hred : a = 0 ∨ ¬ 3 ∣ c) :
    Irreducible (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a)) ↔
      Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) = 1 := by
  constructor
  · exact valuationGCD_eq_one_of_irreducible_normalized_binomial hdodd.pos hc
  · exact irreducible_normalized_binomial_of_odd_of_valuationGCD_eq_one hdodd hred

/-- An irrational exponent with integral output at base three cannot have that output
supported only at the prime three. -/
theorem exists_prime_ne_three_dvd_of_three_rpow_eq_nat_of_irrational
    {β : ℝ} (hβirr : Irrational β) {c : ℕ}
    (hthree : (3 : ℝ) ^ β = (c : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ p ∣ c := by
  by_contra h
  push Not at h
  have hc0 : c ≠ 0 := by
    intro hc
    rw [hc, Nat.cast_zero] at hthree
    exact (Real.rpow_pos_of_pos (by norm_num) _).ne' hthree
  have hcPow : c = 3 ^ c.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd hc0
    intro p hp hpc
    by_contra hp3
    exact h p hp hp3 hpc
  have hβeq : β = (c.primeFactorsList.length : ℝ) := by
    apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 3)).injective
    calc
      (3 : ℝ) ^ β = (c : ℝ) := hthree
      _ = ((3 ^ c.primeFactorsList.length : ℕ) : ℝ) := by exact_mod_cast hcPow
      _ = (3 : ℝ) ^ (c.primeFactorsList.length : ℝ) := by
        rw [Real.rpow_natCast]
        norm_num
  apply hβirr
  refine ⟨(c.primeFactorsList.length : ℚ), ?_⟩
  push_cast
  exact hβeq.symm

/-- Under failure, the reduced numerator in the exact canonical radical is nontrivial
and has a prime divisor other than three, in addition to satisfying the sharp valuation
gcd obstruction and the exact minpoly-degree statement. -/
theorem exists_exact_radical_with_nonthree_numerator_prime
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ w d a c : ℕ, ∃ β : ℝ,
      Odd w ∧ 1 < w ∧ 0 < d ∧ 1 < c ∧
      (a = 0 ∨ ¬ 3 ∣ c) ∧
      oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a ∧
      Irreducible (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a)) ∧
      minpoly ℚ (oddCoreRpow w) =
        X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a) ∧
      (minpoly ℚ (oddCoreRpow w)).natDegree = d ∧
      Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) = 1 ∧
      Irrational β ∧ (3 : ℝ) ^ β = (c : ℝ) ∧
      ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ p ∣ c := by
  obtain ⟨w, d, a, c, β, hwodd, hw, _hwgcd, hd, hc, ha,
      _hindex, hleast, hnorm, _hβdef, _htwo, hthree, hβirr,
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
  obtain ⟨p, hp, hp3, hpc⟩ :=
    exists_prime_ne_three_dvd_of_three_rpow_eq_nat_of_irrational hβirr hthree
  have hc1 : 1 < c := by
    have hple : p ≤ c := Nat.le_of_dvd hc hpc
    exact hp.two_le.trans hple
  exact ⟨w, d, a, c, β, hwodd, hw, hd, hc1, ha, hnorm,
    hirr, hmin, hdeg, hgcd, hβirr, hthree, p, hp, hp3, hpc⟩

private theorem irreducible_double_X_pow_sub_C_of_pos
    {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m : ℕ} {q : K} (hq : 0 < q)
    (hm : Irreducible (X ^ m - C q))
    (hodd : Odd m → ∀ b : K, b ^ 2 ≠ q) :
    Irreducible (X ^ (2 * m) - C q) := by
  apply X_pow_mul_sub_C_irreducible hm
  intro E _ _ x hx
  have hm0 : m ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C hm
  have hxint : IsIntegral K x := not_not.mp fun h ↦ by
    simpa only [degree_zero, degree_X_pow_sub_C (Nat.pos_of_ne_zero hm0),
      WithBot.natCast_ne_bot] using congr_arg degree (hx.symm.trans (dif_neg h))
  apply X_pow_sub_C_irreducible_of_prime (by norm_num : Nat.Prime 2)
  intro b hb
  by_cases hmOdd : Odd m
  · apply hodd hmOdd (Algebra.norm _ b)
    rw [← map_pow, hb, ← adjoin.powerBasis_gen hxint,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    simp [minpoly_gen, hx, hm0.symm, hmOdd.neg_one_pow]
  · have hmEven : Even m := Nat.not_odd_iff_even.mp hmOdd
    have hnorm : (Algebra.norm _ b) ^ 2 = -q := by
      rw [← map_pow, hb, ← adjoin.powerBasis_gen hxint,
        Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
      simp [minpoly_gen, hx, hm0.symm, hmEven.neg_one_pow]
    have hsquare : (0 : K) ≤ (Algebra.norm K b) ^ 2 := sq_nonneg _
    linarith

/-- For a positive reduced rational binomial of any positive degree, the valuation-gcd
condition is sufficient for irreducibility. Positivity removes the exceptional even
Capell factorization: after the first quadratic step, a hypothetical square root would
have a square norm equal to a negative rational. -/
theorem irreducible_normalized_binomial_of_valuationGCD_eq_one
    {d a c : ℕ} (hd : 0 < d) (hc : 0 < c)
    (hred : a = 0 ∨ ¬ 3 ∣ c)
    (hgcd : Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) = 1) :
    Irreducible (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a)) := by
  obtain ⟨k, m, hmOdd, hdm⟩ := Nat.exists_eq_two_pow_mul_odd hd.ne'
  have hmDvd : m ∣ d := by
    refine ⟨2 ^ k, ?_⟩
    rw [hdm, mul_comm]
  have hgmDvd :
      Nat.gcd m (Nat.gcd a (oddPrimeValuationGCD c)) ∣
        Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) :=
    gcd_dvd_gcd hmDvd dvd_rfl
  have hgm : Nat.gcd m (Nat.gcd a (oddPrimeValuationGCD c)) = 1 := by
    apply Nat.dvd_one.mp
    rwa [hgcd] at hgmDvd
  have hbase : Irreducible
      (X ^ m - C ((c : ℚ) / (3 : ℚ) ^ a)) :=
    irreducible_normalized_binomial_of_odd_of_valuationGCD_eq_one hmOdd hred hgm
  rcases k with _ | k
  · rw [hdm]
    simpa using hbase
  · have htwoD : 2 ∣ d := by
      refine ⟨2 ^ k * m, ?_⟩
      rw [hdm, pow_succ]
      ac_rfl
    have hnoSquare : ∀ b : ℚ,
        b ^ 2 ≠ (c : ℚ) / (3 : ℚ) ^ a := by
      intro b hb
      have hroot :=
        (exists_rat_pow_eq_reduced_iff_dvd_denominator_and_valuationGCD hc hred).mp
          ⟨b, hb⟩
      have htwoInner : 2 ∣ Nat.gcd a (oddPrimeValuationGCD c) :=
        Nat.dvd_gcd hroot.1 hroot.2
      have htwoOuter : 2 ∣ Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) :=
        Nat.dvd_gcd htwoD htwoInner
      rw [hgcd] at htwoOuter
      exact (by norm_num : ¬ 2 ∣ 1) htwoOuter
    have hqpos : (0 : ℚ) < (c : ℚ) / (3 : ℚ) ^ a := by
      positivity
    have hiter : ∀ s : ℕ, Irreducible
        (X ^ (2 ^ s * m) - C ((c : ℚ) / (3 : ℚ) ^ a)) := by
      intro s
      induction s with
      | zero => simpa using hbase
      | succ s ih =>
          have hdbl := irreducible_double_X_pow_sub_C_of_pos hqpos ih
            (fun _ ↦ hnoSquare)
          simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdbl
    simpa only [hdm] using hiter (k + 1)

/-- For every positive degree and every reduced positive `c / 3 ^ a`, the normalized
binomial is irreducible exactly when the degree, denominator exponent, and numerator
valuation gcd have no common factor. -/
theorem irreducible_normalized_binomial_iff_valuationGCD_eq_one
    {d a c : ℕ} (hd : 0 < d) (hc : 0 < c)
    (hred : a = 0 ∨ ¬ 3 ∣ c) :
    Irreducible (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a)) ↔
      Nat.gcd d (Nat.gcd a (oddPrimeValuationGCD c)) = 1 := by
  constructor
  · exact valuationGCD_eq_one_of_irreducible_normalized_binomial hd hc
  · exact irreducible_normalized_binomial_of_valuationGCD_eq_one hd hc hred

end

end LeanProofs.TwoBaseIntegerExponent
