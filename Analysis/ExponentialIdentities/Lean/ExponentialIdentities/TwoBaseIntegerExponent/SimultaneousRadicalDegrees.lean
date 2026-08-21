import ExponentialIdentities.TwoBaseIntegerExponent.CanonicalRadicalDivisibleHull
import ExponentialIdentities.TwoBaseIntegerExponent.RadicalDegree
import ExponentialIdentities.TwoBaseIntegerExponent.CanonicalRadicalSharpness
import Mathlib.Data.Rat.Lemmas

/-!
# Exact degrees of simultaneous canonical radicals

The simultaneous primitive normalization gives rational powers of the canonical
radical `E = w ^ (log 3 / log 2)` and its base-swapped companion
`F = v ^ (log 2 / log 3)`. This file proves that the displayed exponents `d`
and `e` are their *least* positive rational-power indices and hence their exact
degrees over `ℚ`.

The key descent is arithmetic: a hypothetical proper index divisor makes the
reduced prime-power denominator and the numerator common perfect powers. It
therefore makes both outputs of the least noninteger solution common perfect
powers, contradicting affine primitivity. The result strengthens the previously
known algebraicity of the swapped radical; it does not assert a contradiction.

When both base-adic depths vanish, the two exact indices are coprime. A
prime-valuation argument then proves that the product `E * F` has exact degree
`d * e`, even when the prime supports of `w` and `v` overlap.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set Polynomial IntermediateField

noncomputable section

private theorem coprime_two_pow_of_reduced {b M : ℕ}
    (hred : b = 0 ∨ ¬ 2 ∣ M) : Nat.Coprime M (2 ^ b) := by
  rcases b.eq_zero_or_pos with rfl | hb
  · simp
  · apply Nat.Coprime.pow_right
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr
      (hred.resolve_left hb.ne')).symm

/-- Reduced numerator/denominator data of a rational power with power-of-two
denominator. -/
private theorem rat_pow_eq_nat_div_two_pow_data
    {M b g : ℕ} (_hM : 0 < M) (_hg : 0 < g)
    (hred : b = 0 ∨ ¬ 2 ∣ M) {q : ℚ}
    (hq : q ^ g = (M : ℚ) / (2 : ℚ) ^ b) :
    g ∣ b ∧ ∃ R : ℕ, M = R ^ g := by
  have hcop : Nat.Coprime M (2 ^ b) := coprime_two_pow_of_reduced hred
  have hdenTarget : ((M : ℚ) / (2 : ℚ) ^ b).den = 2 ^ b := by
    have h := Rat.den_div_eq_of_coprime
      (a := (M : ℤ)) (b := (2 ^ b : ℕ)) (by positivity) (by simpa using hcop)
    norm_num at h ⊢
    exact_mod_cast h
  have hnumTarget : ((M : ℚ) / (2 : ℚ) ^ b).num = (M : ℤ) := by
    have h := Rat.num_div_eq_of_coprime
      (a := (M : ℤ)) (b := (2 ^ b : ℕ)) (by positivity) (by simpa using hcop)
    norm_num at h ⊢
    exact h
  have hden : q.den ^ g = 2 ^ b := by
    rw [← Rat.den_pow, hq, hdenTarget]
  have hnum : q.num ^ g = (M : ℤ) := by
    rw [← Rat.num_pow, hq, hnumTarget]
  have hdenVal := DFunLike.congr_fun
    (congrArg Nat.factorization hden) 2
  have hp2 : Nat.Prime 2 := by norm_num
  simp only [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    hp2.factorization, Finsupp.single_eq_same] at hdenVal
  have hgb : g ∣ b := by
    refine ⟨q.den.factorization 2, ?_⟩
    have hcast : b * 1 = g * q.den.factorization 2 := by
      exact_mod_cast hdenVal.symm
    simpa using hcast
  have hnumAbs := congrArg Int.natAbs hnum
  simp only [Int.natAbs_pow, Int.natAbs_natCast] at hnumAbs
  exact ⟨hgb, q.num.natAbs, hnumAbs.symm⟩

private theorem coprime_three_pow_of_reduced {a B : ℕ}
    (hred : a = 0 ∨ ¬ 3 ∣ B) : Nat.Coprime B (3 ^ a) := by
  rcases a.eq_zero_or_pos with rfl | ha
  · simp
  · apply Nat.Coprime.pow_right
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr
      (hred.resolve_left ha.ne')).symm

private theorem rat_pow_eq_nat_div_three_pow_data
    {B a g : ℕ} (_hB : 0 < B) (_hg : 0 < g)
    (hred : a = 0 ∨ ¬ 3 ∣ B) {q : ℚ}
    (hq : q ^ g = (B : ℚ) / (3 : ℚ) ^ a) :
    g ∣ a ∧ ∃ R : ℕ, B = R ^ g := by
  have hcop : Nat.Coprime B (3 ^ a) := coprime_three_pow_of_reduced hred
  have hdenTarget : ((B : ℚ) / (3 : ℚ) ^ a).den = 3 ^ a := by
    have h := Rat.den_div_eq_of_coprime
      (a := (B : ℤ)) (b := (3 ^ a : ℕ)) (by positivity) (by simpa using hcop)
    norm_num at h ⊢
    exact_mod_cast h
  have hnumTarget : ((B : ℚ) / (3 : ℚ) ^ a).num = (B : ℤ) := by
    have h := Rat.num_div_eq_of_coprime
      (a := (B : ℤ)) (b := (3 ^ a : ℕ)) (by positivity) (by simpa using hcop)
    norm_num at h ⊢
    exact h
  have hden : q.den ^ g = 3 ^ a := by
    rw [← Rat.den_pow, hq, hdenTarget]
  have hnum : q.num ^ g = (B : ℤ) := by
    rw [← Rat.num_pow, hq, hnumTarget]
  have hdenVal := DFunLike.congr_fun
    (congrArg Nat.factorization hden) 3
  have hp3 : Nat.Prime 3 := by norm_num
  simp only [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    hp3.factorization, Finsupp.single_eq_same] at hdenVal
  have hga : g ∣ a := by
    refine ⟨q.den.factorization 3, ?_⟩
    have hcast : a * 1 = g * q.den.factorization 3 := by
      exact_mod_cast hdenVal.symm
    simpa using hcast
  have hnumAbs := congrArg Int.natAbs hnum
  simp only [Int.natAbs_pow, Int.natAbs_natCast] at hnumAbs
  exact ⟨hga, q.num.natAbs, hnumAbs.symm⟩

/-- Coprimality of the prospective mixed-radical degree with the valuation
gcd of its rational power. This remains valid when `w` and `v` have common
prime factors. -/
private theorem mixed_power_valuationGCD_coprime
    {w v d e : ℕ} (hw : 1 < w) (hv : 1 < v)
    (hwprimitive : NatPowerPrimitive w) (hvprimitive : NatPowerPrimitive v)
    (hd : 0 < d) (he : 0 < e) (hde : Nat.Coprime d e) :
    Nat.Coprime (d * e)
      (oddPrimeValuationGCD (v ^ (e ^ 2) * w ^ (d ^ 2))) := by
  let q : ℕ := v ^ (e ^ 2) * w ^ (d ^ 2)
  have hw0 : w ≠ 0 := by omega
  have hv0 : v ≠ 0 := by omega
  have hq0 : q ≠ 0 := by
    dsimp only [q]
    positivity
  have hwgcd : oddPrimeValuationGCD w = 1 :=
    oddPrimeValuationGCD_eq_one_of_natPowerPrimitive hw hwprimitive
  have hvgcd : oddPrimeValuationGCD v = 1 :=
    oddPrimeValuationGCD_eq_one_of_natPowerPrimitive hv hvprimitive
  have hqfac (l : ℕ) :
      q.factorization l =
        e ^ 2 * v.factorization l + d ^ 2 * w.factorization l := by
    dsimp only [q]
    rw [Nat.factorization_mul (pow_ne_zero _ hv0) (pow_ne_zero _ hw0),
      Nat.factorization_pow, Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
    norm_cast
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpde : p ∣ d * e := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpqgcd : p ∣ oddPrimeValuationGCD q :=
    hpg.trans (Nat.gcd_dvd_right _ _)
  have hp_not_e_of_d : p ∣ d → ¬ p ∣ e := by
    intro hpd hpe
    have hpone : p ∣ 1 := by
      rw [← hde.gcd_eq_one]
      exact Nat.dvd_gcd hpd hpe
    exact hp.not_dvd_one hpone
  have hp_not_d_of_e : p ∣ e → ¬ p ∣ d := by
    intro hpe hpd
    exact hp_not_e_of_d hpd hpe
  rcases hp.dvd_mul.mp hpde with hpd | hpe
  · have hex : ∃ l ∈ v.primeFactors, ¬ p ∣ v.factorization l := by
      by_contra hn
      push Not at hn
      have hpone : p ∣ 1 := by
        rw [← hvgcd]
        exact Finset.dvd_gcd hn
      exact hp.not_dvd_one hpone
    obtain ⟨l, hlv, hpvl⟩ := hex
    have hlq : l ∈ q.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨Nat.prime_of_mem_primeFactors hlv, ?_, hq0⟩
      exact (Nat.dvd_of_mem_primeFactors hlv).trans
        ((dvd_pow_self v (by positivity : e ^ 2 ≠ 0)).trans (dvd_mul_right _ _))
    have hpqfac : p ∣ q.factorization l :=
      hpqgcd.trans (Finset.gcd_dvd hlq)
    rw [hqfac] at hpqfac
    have hpdsq : p ∣ d ^ 2 :=
      hpd.trans (dvd_pow_self d (by norm_num : 2 ≠ 0))
    have hpsecond : p ∣ d ^ 2 * w.factorization l :=
      dvd_mul_of_dvd_left hpdsq _
    have hpfirst : p ∣ e ^ 2 * v.factorization l :=
      (Nat.dvd_add_iff_left hpsecond).mpr hpqfac
    rcases hp.dvd_mul.mp hpfirst with hpesq | hpvl'
    · exact (hp_not_e_of_d hpd) (hp.dvd_of_dvd_pow hpesq)
    · exact hpvl hpvl'
  · have hex : ∃ l ∈ w.primeFactors, ¬ p ∣ w.factorization l := by
      by_contra hn
      push Not at hn
      have hpone : p ∣ 1 := by
        rw [← hwgcd]
        exact Finset.dvd_gcd hn
      exact hp.not_dvd_one hpone
    obtain ⟨l, hlw, hpwl⟩ := hex
    have hlq : l ∈ q.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨Nat.prime_of_mem_primeFactors hlw, ?_, hq0⟩
      exact (Nat.dvd_of_mem_primeFactors hlw).trans
        ((dvd_pow_self w (by positivity : d ^ 2 ≠ 0)).trans (dvd_mul_left _ _))
    have hpqfac : p ∣ q.factorization l :=
      hpqgcd.trans (Finset.gcd_dvd hlq)
    rw [hqfac] at hpqfac
    have hpesq : p ∣ e ^ 2 :=
      hpe.trans (dvd_pow_self e (by norm_num : 2 ≠ 0))
    have hpfirst : p ∣ e ^ 2 * v.factorization l :=
      dvd_mul_of_dvd_left hpesq _
    have hpsecond : p ∣ d ^ 2 * w.factorization l :=
      (Nat.dvd_add_iff_right hpfirst).mpr hpqfac
    rcases hp.dvd_mul.mp hpsecond with hpdsq | hpwl'
    · exact (hp_not_d_of_e hpe) (hp.dvd_of_dvd_pow hpdsq)
    · exact hpwl hpwl'

/-- In a simultaneous normalization with a `3`-free second core, `d` is the
exact positive generator of the rational powers of the first radical.  Unlike
the canonical-generator theorem, this conclusion uses only affine primitivity
of the least solution and the reduced simultaneous output equations. -/
theorem oddCoreRpow_exact_rationalPowerIndex_of_simultaneous_normalization
    {beta : ℝ} (hbeta : IsLeastTwoBaseNonintegerSolution beta)
    {a b w v d e : ℕ} (hvthree : ¬ 3 ∣ v) (hw : 0 < w) (hd : 0 < d)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ beta)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ beta)
    (hab : a = 0 ∨ b = 0) :
    (∀ j : ℤ, oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) ↔
        (d : ℤ) ∣ j) ∧
      ∀ j : ℤ, oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) →
        0 < j → (d : ℤ) ≤ j := by
  let B : ℕ := 3 ^ b * v ^ e
  let qE : ℚ := (B : ℚ) / (3 : ℚ) ^ a
  obtain ⟨hnormE, _hnormF⟩ := simultaneous_core_radical_power_normalization hM hB
  have hqEcast : (qE : ℝ) = oddCoreRpow w ^ d := by
    dsimp only [qE, B]
    push_cast
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hnormE.symm
  have hErat : oddCoreRpow w ^ (d : ℤ) ∈
      Set.range ((↑) : ℚ → ℝ) := by
    refine ⟨qE, ?_⟩
    simpa using hqEcast
  obtain ⟨f, hf, _hgroup, hfRat, hiff, hleast⟩ :=
    exists_rationalPowerIndex (oddCoreRpow_pos hw).ne'
      (by exact_mod_cast hd.ne') hErat
  have hfdZ : (f : ℤ) ∣ (d : ℤ) := (hiff (d : ℤ)).mp hErat
  have hfd : f ∣ d := by exact_mod_cast hfdZ
  obtain ⟨g, hdg⟩ := hfd
  have hg : 0 < g := by
    by_contra hg0
    have : g = 0 := Nat.eq_zero_of_not_pos hg0
    rw [hdg, this, mul_zero] at hd
    omega
  obtain ⟨q, hq⟩ := hfRat
  have hqcast : (q : ℝ) = oddCoreRpow w ^ f := by simpa using hq
  have hqpowR : ((q ^ g : ℚ) : ℝ) = (qE : ℝ) := by
    push_cast
    calc
      (q : ℝ) ^ g = (oddCoreRpow w ^ f) ^ g := by rw [← hqcast]
      _ = oddCoreRpow w ^ (f * g) := by rw [pow_mul]
      _ = oddCoreRpow w ^ d := by rw [← hdg]
      _ = (qE : ℝ) := hqEcast.symm
  have hqpow : q ^ g = qE := Rat.cast_injective hqpowR
  have hBpos : 0 < B := by
    have hBreal : (0 : ℝ) < (B : ℝ) := by
      rw [show (B : ℝ) = (3 : ℝ) ^ beta by simpa only [B] using hB]
      positivity
    exact_mod_cast hBreal
  have hred : a = 0 ∨ ¬ 3 ∣ B := by
    rcases hab with ha | rfl
    · exact Or.inl ha
    · right
      dsimp only [B]
      simp only [pow_zero, one_mul]
      exact fun h ↦ hvthree (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
  obtain ⟨hga, R, hBR⟩ :=
    rat_pow_eq_nat_div_three_pow_data hBpos hg hred hqpow
  obtain ⟨t, hat⟩ := hga
  let S : ℕ := 2 ^ t * w ^ f
  have hMS : 2 ^ a * w ^ d = S ^ g := by
    dsimp only [S]
    simp only [hat, hdg, mul_pow, pow_mul]
    have htwo : (2 ^ g) ^ t = (2 ^ t) ^ g := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm g t]
    rw [htwo]
  have hMperfect : ((2 ^ 0 * S ^ g : ℕ) : ℝ) = (2 : ℝ) ^ beta := by
    simp only [pow_zero, one_mul]
    rw [← hMS]
    exact hM
  have hBperfect : ((3 ^ 0 * R ^ g : ℕ) : ℝ) = (3 : ℝ) ^ beta := by
    simp only [pow_zero, one_mul]
    rw [← hBR]
    exact hB
  have hgOne : g = 1 := (hbeta.affine_primitive hg hMperfect hBperfect).2
  have hfeq : f = d := by simpa [hgOne] using hdg.symm
  subst f
  exact ⟨hiff, hleast⟩

/-- The first simultaneous radical also has an exact pure-radical minpoly using
only the reduced simultaneous normalization and least-solution primitivity. -/
theorem oddCoreRpow_exact_radical_degree_of_simultaneous_normalization
    {beta : ℝ} (hbeta : IsLeastTwoBaseNonintegerSolution beta)
    {a b w v d e : ℕ} (hvthree : ¬ 3 ∣ v) (hw : 0 < w) (hd : 0 < d)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ beta)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ beta)
    (hab : a = 0 ∨ b = 0) :
    let q : ℚ := ((3 ^ b * v ^ e : ℕ) : ℚ) / (3 : ℚ) ^ a
    Irreducible (X ^ d - C q) ∧
      minpoly ℚ (oddCoreRpow w) = X ^ d - C q ∧
      (minpoly ℚ (oddCoreRpow w)).natDegree = d := by
  dsimp only
  obtain ⟨_hiff, hleast⟩ :=
    oddCoreRpow_exact_rationalPowerIndex_of_simultaneous_normalization
      hbeta hvthree hw hd hM hB hab
  obtain ⟨hnormE, _hnormF⟩ := simultaneous_core_radical_power_normalization hM hB
  apply irreducible_X_pow_sub_C_of_least_rational_power
      (oddCoreRpow_pos hw) hd
  · rw [hnormE]
    push_cast
    rfl
  · intro n hnRat hn
    have hnRatZ : oddCoreRpow w ^ (n : ℤ) ∈
        Set.range ((↑) : ℚ → ℝ) := by simpa using hnRat
    have hdnZ := hleast (n : ℤ) hnRatZ (by exact_mod_cast hn)
    exact_mod_cast hdnZ

/-- In a simultaneous primitive normalization of the least solution, `e` is
the exact positive generator of the rational powers of the swapped radical. -/
theorem threeFreeCoreRpow_exact_rationalPowerIndex
    {beta : ℝ} (hbeta : IsLeastTwoBaseNonintegerSolution beta)
    {a b w v d e : ℕ} (hwodd : Odd w) (hv : 0 < v) (he : 0 < e)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ beta)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ beta)
    (hab : a = 0 ∨ b = 0) :
    (∀ j : ℤ, threeFreeCoreRpow v ^ j ∈ Set.range ((↑) : ℚ → ℝ) ↔
        (e : ℤ) ∣ j) ∧
      ∀ j : ℤ, threeFreeCoreRpow v ^ j ∈ Set.range ((↑) : ℚ → ℝ) →
        0 < j → (e : ℤ) ≤ j := by
  let M : ℕ := 2 ^ a * w ^ d
  let qF : ℚ := (M : ℚ) / (2 : ℚ) ^ b
  obtain ⟨_hnormE, hnormF⟩ := simultaneous_core_radical_power_normalization hM hB
  have hqFcast : (qF : ℝ) = threeFreeCoreRpow v ^ e := by
    dsimp only [qF, M]
    push_cast
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hnormF.symm
  have hFrat : threeFreeCoreRpow v ^ (e : ℤ) ∈
      Set.range ((↑) : ℚ → ℝ) := by
    refine ⟨qF, ?_⟩
    simpa using hqFcast
  obtain ⟨f, hf, _hgroup, hfRat, hiff, hleast⟩ :=
    exists_rationalPowerIndex (threeFreeCoreRpow_pos hv).ne'
      (by exact_mod_cast he.ne') hFrat
  have hfeZ : (f : ℤ) ∣ (e : ℤ) := (hiff (e : ℤ)).mp hFrat
  have hfe : f ∣ e := by exact_mod_cast hfeZ
  obtain ⟨g, heg⟩ := hfe
  have hg : 0 < g := by
    by_contra hg0
    have : g = 0 := Nat.eq_zero_of_not_pos hg0
    rw [heg, this, mul_zero] at he
    omega
  obtain ⟨q, hq⟩ := hfRat
  have hqcast : (q : ℝ) = threeFreeCoreRpow v ^ f := by
    simpa using hq
  have hqpowR : ((q ^ g : ℚ) : ℝ) = (qF : ℝ) := by
    push_cast
    calc
      (q : ℝ) ^ g = (threeFreeCoreRpow v ^ f) ^ g := by rw [← hqcast]
      _ = threeFreeCoreRpow v ^ (f * g) := by rw [pow_mul]
      _ = threeFreeCoreRpow v ^ e := by rw [← heg]
      _ = (qF : ℝ) := hqFcast.symm
  have hqpow : q ^ g = qF := Rat.cast_injective hqpowR
  have hMpos : 0 < M := by
    have hMreal : (0 : ℝ) < (M : ℝ) := by
      rw [show (M : ℝ) = (2 : ℝ) ^ beta by simpa only [M] using hM]
      positivity
    exact_mod_cast hMreal
  have hred : b = 0 ∨ ¬ 2 ∣ M := by
    rcases hab with rfl | hb
    · right
      dsimp only [M]
      simp only [pow_zero, one_mul]
      exact (hwodd.pow).not_two_dvd_nat
    · exact Or.inl hb
  obtain ⟨hgb, R, hMR⟩ :=
    rat_pow_eq_nat_div_two_pow_data hMpos hg hred hqpow
  obtain ⟨t, hbt⟩ := hgb
  let S : ℕ := 3 ^ t * v ^ f
  have hBS : 3 ^ b * v ^ e = S ^ g := by
    dsimp only [S]
    simp only [hbt, heg, mul_pow, pow_mul]
    have hthree : (3 ^ g) ^ t = (3 ^ t) ^ g := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm g t]
    rw [hthree]
  have hMperfect : ((2 ^ 0 * R ^ g : ℕ) : ℝ) = (2 : ℝ) ^ beta := by
    simp only [pow_zero, one_mul]
    rw [← hMR]
    exact hM
  have hBperfect : ((3 ^ 0 * S ^ g : ℕ) : ℝ) = (3 : ℝ) ^ beta := by
    simp only [pow_zero, one_mul]
    rw [← hBS]
    exact hB
  have hgOne : g = 1 := (hbeta.affine_primitive hg hMperfect hBperfect).2
  have hfeq : f = e := by simpa [hgOne] using heg.symm
  subst f
  exact ⟨hiff, hleast⟩

/-- The symmetric radical has exact pure-radical minpoly and degree `e`. -/
theorem threeFreeCoreRpow_exact_radical_degree_of_simultaneous_normalization
    {beta : ℝ} (hbeta : IsLeastTwoBaseNonintegerSolution beta)
    {a b w v d e : ℕ} (hwodd : Odd w) (hv : 0 < v) (he : 0 < e)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ beta)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ beta)
    (hab : a = 0 ∨ b = 0) :
    let q : ℚ := ((2 ^ a * w ^ d : ℕ) : ℚ) / (2 : ℚ) ^ b
    Irreducible (X ^ e - C q) ∧
      minpoly ℚ (threeFreeCoreRpow v) = X ^ e - C q ∧
      (minpoly ℚ (threeFreeCoreRpow v)).natDegree = e := by
  dsimp only
  obtain ⟨_hiff, hleast⟩ :=
    threeFreeCoreRpow_exact_rationalPowerIndex hbeta hwodd hv he hM hB hab
  obtain ⟨_hnormE, hnormF⟩ := simultaneous_core_radical_power_normalization hM hB
  apply irreducible_X_pow_sub_C_of_least_rational_power
      (threeFreeCoreRpow_pos hv) he
  · rw [hnormF]
    push_cast
    rfl
  · intro n hnRat hn
    have hnRatZ : threeFreeCoreRpow v ^ (n : ℤ) ∈
        Set.range ((↑) : ℚ → ℝ) := by simpa using hnRat
    have henZ := hleast (n : ℤ) hnRatZ (by exact_mod_cast hn)
    exact_mod_cast henZ

/-- If both simultaneous base-adic depths vanish, the product of the two
canonical radicals has exact degree `d * e` over `ℚ`. The conclusion allows
the primitive cores `w` and `v` to have overlapping prime support. -/
theorem mixed_coreRpow_exact_radical_degree_of_zero_baseDepths
    {beta : ℝ} (hbeta : IsLeastTwoBaseNonintegerSolution beta)
    {w v d e : ℕ} (hw : 1 < w) (hv : 1 < v)
    (hwprimitive : NatPowerPrimitive w) (hvprimitive : NatPowerPrimitive v)
    (hd : 0 < d) (he : 0 < e)
    (hM : ((w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ beta)
    (hB : ((v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ beta) :
    let G : ℝ := oddCoreRpow w * threeFreeCoreRpow v
    let q : ℚ := ((v ^ (e ^ 2) * w ^ (d ^ 2) : ℕ) : ℚ)
    Irreducible (X ^ (d * e) - C q) ∧
      minpoly ℚ G = X ^ (d * e) - C q ∧
      (minpoly ℚ G).natDegree = d * e := by
  dsimp only
  have hM' : ((2 ^ 0 * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ beta := by simpa using hM
  have hB' : ((3 ^ 0 * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ beta := by simpa using hB
  have hde : Nat.Coprime d e :=
    hbeta.powerDegrees_coprime_of_equal_baseDepths hd rfl hM' hB'
  obtain ⟨hnormE, hnormF⟩ := simultaneous_core_radical_power_normalization hM' hB'
  have hE : oddCoreRpow w ^ d = ((v ^ e : ℕ) : ℝ) := by simpa using hnormE
  have hF : threeFreeCoreRpow v ^ e = ((w ^ d : ℕ) : ℝ) := by simpa using hnormF
  have hGpow :
      (oddCoreRpow w * threeFreeCoreRpow v) ^ (d * e) =
        ((v ^ (e ^ 2) * w ^ (d ^ 2) : ℕ) : ℝ) := by
    rw [mul_pow]
    calc
      oddCoreRpow w ^ (d * e) * threeFreeCoreRpow v ^ (d * e) =
          (oddCoreRpow w ^ d) ^ e * (threeFreeCoreRpow v ^ e) ^ d := by
            rw [pow_mul, Nat.mul_comm d e, pow_mul]
      _ = (((v ^ e : ℕ) : ℝ) ^ e) * (((w ^ d : ℕ) : ℝ) ^ d) := by
            rw [hE, hF]
      _ = ((v ^ (e ^ 2) * w ^ (d ^ 2) : ℕ) : ℝ) := by
            push_cast
            congr 1 <;> ring
  have hcop := mixed_power_valuationGCD_coprime hw hv hwprimitive hvprimitive hd he hde
  have hgcd :
      Nat.gcd (d * e)
        (Nat.gcd 0 (oddPrimeValuationGCD (v ^ (e ^ 2) * w ^ (d ^ 2)))) = 1 := by
    simpa only [Nat.gcd_zero_left, Nat.coprime_iff_gcd_eq_one] using hcop
  have hirr : Irreducible
      (X ^ (d * e) - C (((v ^ (e ^ 2) * w ^ (d ^ 2) : ℕ) : ℚ)) : ℚ[X]) := by
    simpa using irreducible_normalized_binomial_of_valuationGCD_eq_one
      (Nat.mul_pos hd he) (by positivity : 0 < v ^ (e ^ 2) * w ^ (d ^ 2))
      (Or.inl rfl) hgcd
  have heval : Polynomial.aeval
      (oddCoreRpow w * threeFreeCoreRpow v)
      (X ^ (d * e) - C (((v ^ (e ^ 2) * w ^ (d ^ 2) : ℕ) : ℚ))) = 0 := by
    simp [hGpow]
  have hmonic :
      (X ^ (d * e) - C (((v ^ (e ^ 2) * w ^ (d ^ 2) : ℕ) : ℚ)) : ℚ[X]).Monic :=
    monic_X_pow_sub_C _ (Nat.mul_pos hd he).ne'
  have hmin := minpoly.eq_of_irreducible_of_monic hirr heval hmonic
  refine ⟨hirr, hmin.symm, ?_⟩
  rw [← hmin]
  exact natDegree_X_pow_sub_C

end

end LeanProofs.TwoBaseIntegerExponent
