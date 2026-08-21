import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicBaseUnitPower
import ExponentialIdentities.TwoBaseIntegerExponent.CoreIndependence
import ExponentialIdentities.TwoBaseIntegerExponent.Localization

/-!
# Divisible-hull exclusion for simultaneous canonical radicals

An external prime in the numerator of one rational power prevents every positive
power of the radical from being a rational `2,3`-unit.  Applying this on the two
sides of the simultaneous primitive output normalization gives a transcendental
canonical-radical output under failure of the Alaoglu--Erdos conjecture.

The conclusion is deliberately disjunctive.  The known single-radical normalization
only supplies a numerator prime different from `3`; that prime may be `2`, which is a
genuine exceptional case allowed by the `2,3`-unit hull.  The simultaneous normalization
is what supplies a prime different from both `2` and `3` on at least one side.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- A prime outside `2,3` in the numerator of a rational power excludes the entire
positive `2,3`-unit divisible hull.  The denominator may be supported at either
distinguished prime. -/
theorem not_hasPositiveTwoThreeUnitPower_of_rational_power_external_prime
    {E : ℝ} {d c s a p : ℕ}
    (hs : s = 2 ∨ s = 3) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpc : p ∣ c) (hnorm : E ^ d = (c : ℝ) / (s : ℝ) ^ a) :
    ¬ HasPositiveTwoThreeUnitPower E := by
  rintro ⟨n, hn, q, _hqpos, ⟨i, j, k, l, hq⟩, hEn⟩
  let A : ℕ := 2 ^ i * 3 ^ j
  let B : ℕ := 2 ^ k * 3 ^ l
  let D : ℕ := s ^ a
  have hqcast : (q : ℝ) = (A : ℝ) / (B : ℝ) := by
    rw [hq]
    dsimp only [A, B]
    norm_num
  have hcrossReal :
      ((A : ℝ) / (B : ℝ)) ^ d =
        ((c : ℝ) / (D : ℝ)) ^ n := by
    rw [← hqcast]
    calc
      (q : ℝ) ^ d = (E ^ n) ^ d := by rw [hEn]
      _ = (E ^ d) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((c : ℝ) / (s : ℝ) ^ a) ^ n := by rw [hnorm]
      _ = ((c : ℝ) / (D : ℝ)) ^ n := by
        congr 2
        dsimp only [D]
        norm_num
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hDpos : 0 < D := by
    dsimp only [D]
    rcases hs with rfl | rfl <;> positivity
  have hcrossCast :
      (A : ℝ) ^ d * (D : ℝ) ^ n =
        (c : ℝ) ^ n * (B : ℝ) ^ d := by
    rw [div_pow, div_pow] at hcrossReal
    exact (div_eq_div_iff (pow_ne_zero d (by positivity : (B : ℝ) ≠ 0))
      (pow_ne_zero n (by positivity : (D : ℝ) ≠ 0))).mp hcrossReal
  have hcross : A ^ d * D ^ n = c ^ n * B ^ d := by
    exact_mod_cast hcrossCast
  have hpcn : p ∣ c ^ n := hpc.trans (dvd_pow_self c hn.ne')
  have hpLeft : p ∣ A ^ d * D ^ n := by
    rw [hcross]
    exact dvd_mul_of_dvd_left hpcn _
  rcases hp.dvd_mul.mp hpLeft with hpA | hpD
  · have hpA' : p ∣ A := hp.dvd_of_dvd_pow hpA
    dsimp only [A] at hpA'
    rcases hp.dvd_mul.mp hpA' with hpTwoPow | hpThreePow
    · have hpTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpTwoPow
      exact hp2 (((Nat.dvd_prime Nat.prime_two).mp hpTwo).resolve_left hp.ne_one)
    · have hpThree : p ∣ 3 := hp.dvd_of_dvd_pow hpThreePow
      exact hp3 (((Nat.dvd_prime Nat.prime_three).mp hpThree).resolve_left hp.ne_one)
  · have hpD' : p ∣ D := hp.dvd_of_dvd_pow hpD
    dsimp only [D] at hpD'
    have hps : p ∣ s := hp.dvd_of_dvd_pow hpD'
    rcases hs with rfl | rfl
    · exact hp2 (((Nat.dvd_prime Nat.prime_two).mp hps).resolve_left hp.ne_one)
    · exact hp3 (((Nat.dvd_prime Nat.prime_three).mp hps).resolve_left hp.ne_one)

/-- The symmetric radical attached to the `3`-free core of the base-three output. -/
def threeFreeCoreRpow (v : ℕ) : ℝ := (v : ℝ) ^ logTwoDivLogThree

theorem threeFreeCoreRpow_pos {v : ℕ} (hv : 0 < v) :
    0 < threeFreeCoreRpow v :=
  Real.rpow_pos_of_pos (by exact_mod_cast hv) _

private theorem three_rpow_logTwoDivLogThree :
    (3 : ℝ) ^ logTwoDivLogThree = 2 := by
  have hlog3 : Real.log (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), logTwoDivLogThree]
  have hmul : Real.log (3 : ℝ) * (Real.log (2 : ℝ) / Real.log (3 : ℝ)) =
      Real.log (2 : ℝ) := by field_simp
  rw [hmul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Symmetric common-core identity for the base-three output. -/
theorem threeFreeCandidateRpow_eq_two_pow_mul_threeFreeCoreRpow_pow
    {v b e N : ℕ} (hN : N = 3 ^ b * v ^ e) :
    (N : ℝ) ^ logTwoDivLogThree =
      (2 : ℝ) ^ b * threeFreeCoreRpow v ^ e := by
  subst N
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) logTwoDivLogThree b,
    ← Real.rpow_pow_comm (Nat.cast_nonneg v) logTwoDivLogThree e,
    three_rpow_logTwoDivLogThree]
  rfl

private theorem two_rpow_rpow_logThreeDivLogTwo (x : ℝ) :
    ((2 : ℝ) ^ x) ^ logThreeDivLogTwo = (3 : ℝ) ^ x := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), two_rpow_logThreeDivLogTwo]

private theorem three_rpow_rpow_logTwoDivLogThree (x : ℝ) :
    ((3 : ℝ) ^ x) ^ logTwoDivLogThree = (2 : ℝ) ^ x := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), mul_comm,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), three_rpow_logTwoDivLogThree]

/-- The two log-ratio radicals attached to a simultaneous output normalization have
the displayed rational powers. -/
theorem simultaneous_core_radical_power_normalization
    {beta : ℝ} {a b w v d e : ℕ}
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ beta)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ beta) :
    oddCoreRpow w ^ d =
        ((3 ^ b * v ^ e : ℕ) : ℝ) / (3 : ℝ) ^ a ∧
      threeFreeCoreRpow v ^ e =
        ((2 ^ a * w ^ d : ℕ) : ℝ) / (2 : ℝ) ^ b := by
  have hMtoB :
      (((2 ^ a * w ^ d : ℕ) : ℝ) ^ logThreeDivLogTwo) =
        ((3 ^ b * v ^ e : ℕ) : ℝ) := by
    rw [hM, two_rpow_rpow_logThreeDivLogTwo beta, ← hB]
  have hBtoM :
      (((3 ^ b * v ^ e : ℕ) : ℝ) ^ logTwoDivLogThree) =
        ((2 ^ a * w ^ d : ℕ) : ℝ) := by
    rw [hB, three_rpow_rpow_logTwoDivLogThree beta, ← hM]
  constructor
  · apply (eq_div_iff (pow_ne_zero a (by norm_num : (3 : ℝ) ≠ 0))).2
    rw [mul_comm]
    exact (candidateRpow_eq_three_pow_mul_oddCoreRpow_pow
      (m := 2 ^ a * w ^ d) (w := w) (i := a) (j := d) rfl).symm.trans hMtoB
  · apply (eq_div_iff (pow_ne_zero b (by norm_num : (2 : ℝ) ≠ 0))).2
    rw [mul_comm]
    exact (threeFreeCandidateRpow_eq_two_pow_mul_threeFreeCoreRpow_pow
      (N := 3 ^ b * v ^ e) (v := v) (b := b) (e := e) rfl).symm.trans hBtoM

/-- Under failure, the two simultaneous primitive output cores determine two positive
algebraic log-ratio radicals.  An external prime in one output core forces the radical
on the opposite side outside the entire positive rational `2,3`-unit divisible hull.
Consequently at least one of the two canonical radical outputs at the least solution is
transcendental.  No corresponding assertion is made about each radical separately. -/
theorem exists_simultaneous_canonical_radical_divisibleHull_exclusion
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
      (¬ HasPositiveTwoThreeUnitPower (oddCoreRpow w) ∨
        ¬ HasPositiveTwoThreeUnitPower (threeFreeCoreRpow v)) ∧
      (Transcendental ℚ ((oddCoreRpow w) ^ beta) ∨
        Transcendental ℚ ((threeFreeCoreRpow v) ^ beta)) := by
  obtain ⟨beta, a, b, w, v, d, e, hbetaIrr, hbetaLeast, hwodd, hw,
      hwprimitive, hvthree, hv, hvprimitive, hd, he, hM, hB, hab,
      hexternal⟩ :=
    exists_external_prime_in_simultaneous_primitive_output_cores hfail
  obtain ⟨hnormE, hnormF⟩ := simultaneous_core_radical_power_normalization hM hB
  let qE : ℚ := ((3 ^ b * v ^ e : ℕ) : ℚ) / (3 : ℚ) ^ a
  have hqEcast : (qE : ℝ) = oddCoreRpow w ^ d := by
    dsimp only [qE]
    push_cast
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hnormE.symm
  have hEalg : IsAlgebraic ℚ (oddCoreRpow w) := by
    apply IsAlgebraic.of_pow hd
    rw [← hqEcast]
    exact isAlgebraic_rat ℚ qE
  let qF : ℚ := ((2 ^ a * w ^ d : ℕ) : ℚ) / (2 : ℚ) ^ b
  have hqFcast : (qF : ℝ) = threeFreeCoreRpow v ^ e := by
    dsimp only [qF]
    push_cast
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hnormF.symm
  have hFalg : IsAlgebraic ℚ (threeFreeCoreRpow v) := by
    apply IsAlgebraic.of_pow he
    rw [← hqFcast]
    exact isAlgebraic_rat ℚ qF
  have hEpos : 0 < oddCoreRpow w := oddCoreRpow_pos (by omega)
  have hFpos : 0 < threeFreeCoreRpow v := threeFreeCoreRpow_pos (by omega)
  refine ⟨beta, a, b, w, v, d, e, hbetaIrr, hbetaLeast, hwodd, hw,
    hwprimitive, hvthree, hv, hvprimitive, hd, he, hM, hB, hab,
    hnormE, hnormF, hEalg, hFalg, hexternal, ?_⟩
  rcases hexternal with hwext | hvext
  · obtain ⟨p, hp, hpw, hp2, hp3⟩ := hwext
    have hpM : p ∣ 2 ^ a * w ^ d :=
      dvd_mul_of_dvd_right (hpw.trans (dvd_pow_self w hd.ne')) _
    have hnoF : ¬ HasPositiveTwoThreeUnitPower (threeFreeCoreRpow v) :=
      not_hasPositiveTwoThreeUnitPower_of_rational_power_external_prime
        (E := threeFreeCoreRpow v) (d := e) (c := 2 ^ a * w ^ d)
        (s := 2) (a := b) (p := p) (Or.inl rfl) hp hp2 hp3 hpM hnormF
    exact ⟨Or.inr hnoF, Or.inr
      (hbetaLeast.1.transcendental_real_rpow_of_no_positiveTwoThreeUnitPower
        hFpos hFalg hnoF)⟩
  · obtain ⟨p, hp, hpv, hp2, hp3⟩ := hvext
    have hpB : p ∣ 3 ^ b * v ^ e :=
      dvd_mul_of_dvd_right (hpv.trans (dvd_pow_self v he.ne')) _
    have hnoE : ¬ HasPositiveTwoThreeUnitPower (oddCoreRpow w) :=
      not_hasPositiveTwoThreeUnitPower_of_rational_power_external_prime
        (E := oddCoreRpow w) (d := d) (c := 3 ^ b * v ^ e)
        (s := 3) (a := a) (p := p) (Or.inr rfl) hp hp2 hp3 hpB hnormE
    exact ⟨Or.inl hnoE, Or.inl
      (hbetaLeast.1.transcendental_real_rpow_of_no_positiveTwoThreeUnitPower
        hEpos hEalg hnoE)⟩

end

end LeanProofs.TwoBaseIntegerExponent
