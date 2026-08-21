import ExponentialIdentities.TwoBaseIntegerExponent.CanonicalRadicalDivisibleHull

/-!
# Mixed canonical-radical output transcendence

Under a hypothetical counterexample, the two canonical radicals may individually lie in the
positive rational `2,3`-unit divisible hull.  Every genuinely mixed positive monomial in
them nevertheless retains an external prime in a rational power.  Consequently all of its
outputs at the least nonintegral solution are transcendental.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- A rational power whose numerator has an external prime and whose denominator does not
have that prime excludes every positive rational `2,3`-unit power. -/
theorem not_hasPositiveTwoThreeUnitPower_of_rational_power_external_prime_denominator
    {G : ℝ} {d c D p : ℕ}
    (_hd : 0 < d) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpc : p ∣ c) (hpD : ¬ p ∣ D) (hD : 0 < D)
    (hnorm : G ^ d = (c : ℝ) / (D : ℝ)) :
    ¬ HasPositiveTwoThreeUnitPower G := by
  rintro ⟨n, hn, q, _hqpos, ⟨i, j, k, l, hq⟩, hGn⟩
  let A : ℕ := 2 ^ i * 3 ^ j
  let B : ℕ := 2 ^ k * 3 ^ l
  have hqcast : (q : ℝ) = (A : ℝ) / (B : ℝ) := by
    rw [hq]
    dsimp only [A, B]
    norm_num
  have hcrossReal :
      ((A : ℝ) / (B : ℝ)) ^ d =
        ((c : ℝ) / (D : ℝ)) ^ n := by
    rw [← hqcast]
    calc
      (q : ℝ) ^ d = (G ^ n) ^ d := by rw [hGn]
      _ = (G ^ d) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((c : ℝ) / (D : ℝ)) ^ n := by rw [hnorm]
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hcrossCast :
      (A : ℝ) ^ d * (D : ℝ) ^ n =
        (c : ℝ) ^ n * (B : ℝ) ^ d := by
    rw [div_pow, div_pow] at hcrossReal
    exact (div_eq_div_iff (pow_ne_zero d (by positivity : (B : ℝ) ≠ 0))
      (pow_ne_zero n (by exact_mod_cast hD.ne' : (D : ℝ) ≠ 0))).mp hcrossReal
  have hcross : A ^ d * D ^ n = c ^ n * B ^ d := by
    exact_mod_cast hcrossCast
  have hpcn : p ∣ c ^ n := hpc.trans (dvd_pow_self c hn.ne')
  have hpLeft : p ∣ A ^ d * D ^ n := by
    rw [hcross]
    exact dvd_mul_of_dvd_left hpcn _
  rcases hp.dvd_mul.mp hpLeft with hpA | hpDn
  · have hpA' : p ∣ A := hp.dvd_of_dvd_pow hpA
    dsimp only [A] at hpA'
    rcases hp.dvd_mul.mp hpA' with hpTwoPow | hpThreePow
    · have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpTwoPow
      exact hp2 (((Nat.dvd_prime Nat.prime_two).mp hpTwo).resolve_left hp.ne_one)
    · have hpThree : p ∣ 3 := hp.dvd_of_dvd_pow hpThreePow
      exact hp3 (((Nat.dvd_prime Nat.prime_three).mp hpThree).resolve_left hp.ne_one)
  · have hpD' : p ∣ D := hp.dvd_of_dvd_pow hpDn
    exact hpD hpD'

private theorem mixed_pow_normalization
    {E F : ℝ} {d e cE cF DE DF i j : ℕ}
    (hE : E ^ d = (cE : ℝ) / (DE : ℝ))
    (hF : F ^ e = (cF : ℝ) / (DF : ℝ)) :
    (E ^ i * F ^ j) ^ (d * e) =
      ((cE ^ (i * e) * cF ^ (j * d) : ℕ) : ℝ) /
        ((DE ^ (i * e) * DF ^ (j * d) : ℕ) : ℝ) := by
  have hEi : (E ^ i) ^ (d * e) = (E ^ d) ^ (i * e) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hFj : (F ^ j) ^ (d * e) = (F ^ e) ^ (j * d) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [mul_pow, hEi, hFj, hE, hF, div_pow, div_pow]
  norm_num only [Nat.cast_mul, Nat.cast_pow]
  field_simp

/-- If one numerator of two rational powers has an external prime absent from both
denominators, then every positive mixed monomial lies outside the rational `2,3`-unit hull. -/
theorem not_hasPositiveTwoThreeUnitPower_mixed_of_rational_powers_external_prime
    {E F : ℝ} {d e cE cF DE DF p i j : ℕ}
    (hd : 0 < d) (he : 0 < e) (hi : 0 < i) (hj : 0 < j)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpc : p ∣ cE ∨ p ∣ cF)
    (hpDE : ¬ p ∣ DE) (hpDF : ¬ p ∣ DF)
    (hDE : 0 < DE) (hDF : 0 < DF)
    (hE : E ^ d = (cE : ℝ) / (DE : ℝ))
    (hF : F ^ e = (cF : ℝ) / (DF : ℝ)) :
    ¬ HasPositiveTwoThreeUnitPower (E ^ i * F ^ j) := by
  let c : ℕ := cE ^ (i * e) * cF ^ (j * d)
  let D : ℕ := DE ^ (i * e) * DF ^ (j * d)
  have hie : 0 < i * e := Nat.mul_pos hi he
  have hjd : 0 < j * d := Nat.mul_pos hj hd
  have hpc' : p ∣ c := by
    dsimp only [c]
    rcases hpc with hpE | hpF
    · exact dvd_mul_of_dvd_left (hpE.trans (dvd_pow_self cE hie.ne')) _
    · exact dvd_mul_of_dvd_right (hpF.trans (dvd_pow_self cF hjd.ne')) _
  have hpD : ¬ p ∣ D := by
    intro hpDall
    dsimp only [D] at hpDall
    rcases hp.dvd_mul.mp hpDall with hpDEpow | hpDFpow
    · exact hpDE (hp.dvd_of_dvd_pow hpDEpow)
    · exact hpDF (hp.dvd_of_dvd_pow hpDFpow)
  have hD : 0 < D := by dsimp only [D]; positivity
  apply not_hasPositiveTwoThreeUnitPower_of_rational_power_external_prime_denominator
    (d := d * e) (c := c) (D := D) (p := p)
      (Nat.mul_pos hd he) hp hp2 hp3 hpc' hpD hD
  exact mixed_pow_normalization hE hF

/-- Every positive mixed monomial in the two canonical radicals has transcendental
output at a nonintegral two-base solution, provided one simultaneous core has an
external prime.  Individual radicals may still be exceptional; mixing them prevents
that exception. -/
theorem TwoBaseNonintegerSolution.transcendental_mixed_canonical_radical_output
    {beta : ℝ} (hbeta : TwoBaseNonintegerSolution beta)
    {a b w v d e i j : ℕ}
    (hd : 0 < d) (he : 0 < e) (hi : 0 < i) (hj : 0 < j)
    (hnormE : oddCoreRpow w ^ d =
      ((3 ^ b * v ^ e : ℕ) : ℝ) / (3 : ℝ) ^ a)
    (hnormF : threeFreeCoreRpow v ^ e =
      ((2 ^ a * w ^ d : ℕ) : ℝ) / (2 : ℝ) ^ b)
    (hEpos : 0 < oddCoreRpow w) (hFpos : 0 < threeFreeCoreRpow v)
    (hEalg : IsAlgebraic ℚ (oddCoreRpow w))
    (hFalg : IsAlgebraic ℚ (threeFreeCoreRpow v))
    (hexternal :
      (∃ p : ℕ, p.Prime ∧ p ∣ w ∧ p ≠ 2 ∧ p ≠ 3) ∨
        ∃ p : ℕ, p.Prime ∧ p ∣ v ∧ p ≠ 2 ∧ p ≠ 3) :
    Transcendental ℚ
      ((oddCoreRpow w ^ i * threeFreeCoreRpow v ^ j) ^ beta) := by
  have hnormE' : oddCoreRpow w ^ d =
      ((3 ^ b * v ^ e : ℕ) : ℝ) / ((3 ^ a : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnormE
  have hnormF' : threeFreeCoreRpow v ^ e =
      ((2 ^ a * w ^ d : ℕ) : ℝ) / ((2 ^ b : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnormF
  have hno : ¬ HasPositiveTwoThreeUnitPower
      (oddCoreRpow w ^ i * threeFreeCoreRpow v ^ j) := by
    rcases hexternal with hwext | hvext
    · obtain ⟨p, hp, hpw, hp2, hp3⟩ := hwext
      have hpcF : p ∣ 2 ^ a * w ^ d :=
        dvd_mul_of_dvd_right (hpw.trans (dvd_pow_self w hd.ne')) _
      have hpThreePow : ¬ p ∣ 3 ^ a := by
        intro hpa
        have hpThree : p ∣ 3 := hp.dvd_of_dvd_pow hpa
        exact hp3 (((Nat.dvd_prime Nat.prime_three).mp hpThree).resolve_left hp.ne_one)
      have hpTwoPow : ¬ p ∣ 2 ^ b := by
        intro hpb
        have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpb
        exact hp2 (((Nat.dvd_prime Nat.prime_two).mp hpTwo).resolve_left hp.ne_one)
      exact not_hasPositiveTwoThreeUnitPower_mixed_of_rational_powers_external_prime
        (E := oddCoreRpow w) (F := threeFreeCoreRpow v)
        (d := d) (e := e) (cE := 3 ^ b * v ^ e) (cF := 2 ^ a * w ^ d)
        (DE := 3 ^ a) (DF := 2 ^ b) (p := p) (i := i) (j := j)
        hd he hi hj hp hp2 hp3 (Or.inr hpcF) hpThreePow hpTwoPow
        (by positivity) (by positivity) hnormE' hnormF'
    · obtain ⟨p, hp, hpv, hp2, hp3⟩ := hvext
      have hpcE : p ∣ 3 ^ b * v ^ e :=
        dvd_mul_of_dvd_right (hpv.trans (dvd_pow_self v he.ne')) _
      have hpThreePow : ¬ p ∣ 3 ^ a := by
        intro hpa
        have hpThree : p ∣ 3 := hp.dvd_of_dvd_pow hpa
        exact hp3 (((Nat.dvd_prime Nat.prime_three).mp hpThree).resolve_left hp.ne_one)
      have hpTwoPow : ¬ p ∣ 2 ^ b := by
        intro hpb
        have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpb
        exact hp2 (((Nat.dvd_prime Nat.prime_two).mp hpTwo).resolve_left hp.ne_one)
      exact not_hasPositiveTwoThreeUnitPower_mixed_of_rational_powers_external_prime
        (E := oddCoreRpow w) (F := threeFreeCoreRpow v)
        (d := d) (e := e) (cE := 3 ^ b * v ^ e) (cF := 2 ^ a * w ^ d)
        (DE := 3 ^ a) (DF := 2 ^ b) (p := p) (i := i) (j := j)
        hd he hi hj hp hp2 hp3 (Or.inl hpcE) hpThreePow hpTwoPow
        (by positivity) (by positivity) hnormE' hnormF'
  exact hbeta.transcendental_real_rpow_of_no_positiveTwoThreeUnitPower
    (mul_pos (pow_pos hEpos i) (pow_pos hFpos j))
    ((hEalg.pow i).mul (hFalg.pow j)) hno

/-- Algebraic outputs among nonnegative mixed canonical-radical monomials can
occur only on one of the two coordinate axes. The behavior on the individual
axes is deliberately left open. -/
theorem TwoBaseNonintegerSolution.algebraic_mixed_canonical_radical_output_imp_coordinate_face
    {beta : ℝ} (hbeta : TwoBaseNonintegerSolution beta)
    {a b w v d e i j : ℕ}
    (hd : 0 < d) (he : 0 < e)
    (hnormE : oddCoreRpow w ^ d =
      ((3 ^ b * v ^ e : ℕ) : ℝ) / (3 : ℝ) ^ a)
    (hnormF : threeFreeCoreRpow v ^ e =
      ((2 ^ a * w ^ d : ℕ) : ℝ) / (2 : ℝ) ^ b)
    (hEpos : 0 < oddCoreRpow w) (hFpos : 0 < threeFreeCoreRpow v)
    (hEalg : IsAlgebraic ℚ (oddCoreRpow w))
    (hFalg : IsAlgebraic ℚ (threeFreeCoreRpow v))
    (hexternal :
      (∃ p : ℕ, p.Prime ∧ p ∣ w ∧ p ≠ 2 ∧ p ≠ 3) ∨
        ∃ p : ℕ, p.Prime ∧ p ∣ v ∧ p ≠ 2 ∧ p ≠ 3)
    (hAlg : IsAlgebraic ℚ
      ((oddCoreRpow w ^ i * threeFreeCoreRpow v ^ j) ^ beta)) :
    i = 0 ∨ j = 0 := by
  by_contra hface
  push Not at hface
  exact (hbeta.transcendental_mixed_canonical_radical_output hd he
    (Nat.pos_of_ne_zero hface.1) (Nat.pos_of_ne_zero hface.2)
    hnormE hnormF hEpos hFpos hEalg hFalg hexternal) hAlg

/-- Failure of Alaoglu--Erdos supplies simultaneous canonical radicals for which
all genuinely mixed positive monomials have transcendental output at the least
nonintegral solution. -/
theorem exists_simultaneous_canonical_radical_mixed_output_transcendence
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ beta : ℝ, ∃ a b w v d e : ℕ,
      Irrational beta ∧ IsLeastTwoBaseNonintegerSolution beta ∧
      Odd w ∧ 1 < w ∧ NatPowerPrimitive w ∧
      ¬ 3 ∣ v ∧ 1 < v ∧ NatPowerPrimitive v ∧
      0 < d ∧ 0 < e ∧
      ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ beta ∧
      ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ beta ∧
      (a = 0 ∨ b = 0) ∧
      oddCoreRpow w ^ d =
        ((3 ^ b * v ^ e : ℕ) : ℝ) / (3 : ℝ) ^ a ∧
      threeFreeCoreRpow v ^ e =
        ((2 ^ a * w ^ d : ℕ) : ℝ) / (2 : ℝ) ^ b ∧
      IsAlgebraic ℚ (oddCoreRpow w) ∧
      IsAlgebraic ℚ (threeFreeCoreRpow v) ∧
      ((∃ p : ℕ, p.Prime ∧ p ∣ w ∧ p ≠ 2 ∧ p ≠ 3) ∨
        ∃ p : ℕ, p.Prime ∧ p ∣ v ∧ p ≠ 2 ∧ p ≠ 3) ∧
      ∀ i j : ℕ, 0 < i → 0 < j →
        Transcendental ℚ
          ((oddCoreRpow w ^ i * threeFreeCoreRpow v ^ j) ^ beta) := by
  obtain ⟨beta, a, b, w, v, d, e, hbetaIrr, hbetaLeast,
      hwodd, hw, hwprimitive, hvthree, hv, hvprimitive, hd, he,
      hM, hB, hab, hnormE, hnormF, hEalg, hFalg, hexternal, _hno, _htrans⟩ :=
    exists_simultaneous_canonical_radical_divisibleHull_exclusion hfail
  have hEpos : 0 < oddCoreRpow w := oddCoreRpow_pos (by omega)
  have hFpos : 0 < threeFreeCoreRpow v := threeFreeCoreRpow_pos (by omega)
  refine ⟨beta, a, b, w, v, d, e, hbetaIrr, hbetaLeast,
    hwodd, hw, hwprimitive, hvthree, hv, hvprimitive, hd, he,
    hM, hB, hab, hnormE, hnormF, hEalg, hFalg, hexternal, ?_⟩
  intro i j hi hj
  exact hbetaLeast.1.transcendental_mixed_canonical_radical_output
    hd he hi hj hnormE hnormF hEpos hFpos hEalg hFalg hexternal

end

end LeanProofs.TwoBaseIntegerExponent
