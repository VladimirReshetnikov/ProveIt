import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveGenerator
import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveRadical
import ExponentialIdentities.TwoBaseIntegerExponent.FiniteCheck4096
import Mathlib.Data.Nat.ModEq

namespace LeanProofs.TwoBaseIntegerExponent

open Set Finset

noncomputable section

/-- Taking a positive power scales the gcd of the prime valuations by the exponent. -/
theorem oddPrimeValuationGCD_pow {w d : ℕ} (hd : d ≠ 0) :
    oddPrimeValuationGCD (w ^ d) = d * oddPrimeValuationGCD w := by
  unfold oddPrimeValuationGCD
  rw [Nat.primeFactors_pow w hd, Nat.factorization_pow]
  change w.primeFactors.gcd (fun p => d * w.factorization p) =
    d * w.primeFactors.gcd w.factorization
  simpa only [normalize_eq] using
    (Finset.gcd_mul_left (β := ℕ) (α := ℕ)
      (s := w.primeFactors) (f := w.factorization) (a := d))

/-- In a prime-power times primitive-power normalization, the outer power degree is
recoverable intrinsically as the valuation gcd of the prime-free part. -/
theorem valuationGCD_ordCompl_primePower_mul_primitivePower
    {p a w d : ℕ} (hp : p.Prime) (hpw : ¬ p ∣ w)
    (hwgcd : oddPrimeValuationGCD w = 1) (hd : 0 < d) :
    oddPrimeValuationGCD (ordCompl[p] (p ^ a * w ^ d)) = d := by
  have hpwd : ¬ p ∣ w ^ d := fun h ↦ hpw (hp.dvd_of_dvd_pow h)
  rw [Nat.ordCompl_pow_mul_of_not_dvd a hp hpwd,
    oddPrimeValuationGCD_pow hd.ne', hwgcd, mul_one]

/-- If the two outputs of a least noninteger solution have power decompositions whose
outer exponents have a common divisor `k`, then their base-adic exponents cannot be
congruent modulo `k` unless `k = 1`. -/
theorem IsLeastTwoBaseNonintegerSolution.common_coordinate_modulus_eq_one
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b w v d e k : ℕ} (hk : 0 < k) (hkd : k ∣ d) (hke : k ∣ e)
    (hab : a ≡ b [MOD k])
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    k = 1 := by
  obtain ⟨d₀, rfl⟩ := hkd
  obtain ⟨e₀, rfl⟩ := hke
  let r := a % k
  have habmod : a % k = b % k := hab
  have ha : a = r + (a / k) * k := by
    dsimp only [r]
    simpa only [mul_comm] using (Nat.mod_add_div a k).symm
  have hb : b = r + (b / k) * k := by
    dsimp only [r]
    rw [habmod]
    simpa only [mul_comm] using (Nat.mod_add_div b k).symm
  have hMdecomp :
      2 ^ a * w ^ (k * d₀) =
        2 ^ r * (2 ^ (a / k) * w ^ d₀) ^ k := by
    conv_lhs => rw [ha, mul_comm k d₀]
    symm
    rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [← mul_assoc, ← pow_add]
  have hBdecomp :
      3 ^ b * v ^ (k * e₀) =
        3 ^ r * (3 ^ (b / k) * v ^ e₀) ^ k := by
    conv_lhs => rw [hb, mul_comm k e₀]
    symm
    rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [← mul_assoc, ← pow_add]
  have hM' :
      (((2 ^ r * (2 ^ (a / k) * w ^ d₀) ^ k : ℕ)) : ℝ) =
        (2 : ℝ) ^ β := by
    rw [← hMdecomp]
    exact hM
  have hB' :
      (((3 ^ r * (3 ^ (b / k) * v ^ e₀) ^ k : ℕ)) : ℝ) =
        (3 : ℝ) ^ β := by
    rw [← hBdecomp]
    exact hB
  exact (hβ.affine_primitive hk hM' hB').2

/-- The intrinsic obstruction measured by simultaneous power degrees and the difference
of the two base-adic exponents. -/
def simultaneousCoordinateGCD (a b d e : ℕ) : ℕ :=
  Nat.gcd (Nat.gcd d e) (((b : ℤ) - (a : ℤ)).natAbs)

/-- For any power decompositions of the two least outputs, the two outer power degrees
and the difference of the base-adic exponents have gcd one. -/
theorem IsLeastTwoBaseNonintegerSolution.simultaneousCoordinateGCD_eq_one
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b w v d e : ℕ} (hd : 0 < d)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    simultaneousCoordinateGCD a b d e = 1 := by
  let g := simultaneousCoordinateGCD a b d e
  have hgde : g ∣ Nat.gcd d e := by
    exact Nat.gcd_dvd_left _ _
  have hgd : g ∣ d := hgde.trans (Nat.gcd_dvd_left d e)
  have hge : g ∣ e := hgde.trans (Nat.gcd_dvd_right d e)
  have hgdist : g ∣ ((b : ℤ) - (a : ℤ)).natAbs := by
    exact Nat.gcd_dvd_right _ _
  have hgpos : 0 < g := by
    apply Nat.gcd_pos_of_pos_left
    exact Nat.gcd_pos_of_pos_left e hd
  have hab : a ≡ b [MOD g] := by
    apply Nat.modEq_iff_dvd.mpr
    apply Int.dvd_natAbs.mp
    exact_mod_cast hgdist
  exact hβ.common_coordinate_modulus_eq_one hgpos hgd hge hab hM hB

/-- A prime common to the two outer power degrees forces distinct base-adic depths modulo
that prime. -/
theorem IsLeastTwoBaseNonintegerSolution.baseDepths_not_modEq_of_common_prime_powerDegree
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b w v d e p : ℕ} (hp : p.Prime) (hpd : p ∣ d) (hpe : p ∣ e)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    ¬ a ≡ b [MOD p] := by
  intro hab
  exact hp.ne_one (hβ.common_coordinate_modulus_eq_one hp.pos hpd hpe hab hM hB)

/-- Equal base-adic depths force the two outer power degrees to be coprime. -/
theorem IsLeastTwoBaseNonintegerSolution.powerDegrees_coprime_of_equal_baseDepths
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b w v d e : ℕ} (hd : 0 < d) (hab : a = b)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    Nat.Coprime d e := by
  subst b
  have hsim := hβ.simultaneousCoordinateGCD_eq_one hd hM hB
  simpa [simultaneousCoordinateGCD, Nat.coprime_iff_gcd_eq_one] using hsim

/-- If both outputs have the same outer power degree, that degree is coprime to the
difference of their base-adic depths. -/
theorem IsLeastTwoBaseNonintegerSolution.same_powerDegree_coprime_depthDifference
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b w v d : ℕ} (hd : 0 < d)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ d : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    Nat.Coprime d (((b : ℤ) - (a : ℤ)).natAbs) := by
  have hsim := hβ.simultaneousCoordinateGCD_eq_one hd hM hB
  simpa [simultaneousCoordinateGCD, Nat.coprime_iff_gcd_eq_one] using hsim

/-- Matching base-adic depths and matching outer degrees are possible only in degree one. -/
theorem IsLeastTwoBaseNonintegerSolution.same_powerDegree_eq_one_of_equal_baseDepths
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β)
    {a b w v d : ℕ} (hd : 0 < d) (hab : a = b)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ d : ℕ) : ℝ) = (3 : ℝ) ^ β) :
    d = 1 := by
  exact (Nat.coprime_self d).mp
    (hβ.powerDegrees_coprime_of_equal_baseDepths hd hab hM hB)

/-- Failure of the conjecture yields simultaneous primitive-power normalizations of both
least outputs.  Their power degrees are intrinsic valuation gcds of the complementary
parts, and together with the difference of the base-adic depths they have gcd one. -/
theorem exists_simultaneous_primitive_output_normalization
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ, ∃ a b w v d e : ℕ,
      Irrational β ∧ IsLeastTwoBaseNonintegerSolution β ∧
      Odd w ∧ 1 < w ∧ NatPowerPrimitive w ∧
      ¬ 3 ∣ v ∧ 1 < v ∧ NatPowerPrimitive v ∧
      0 < d ∧ 0 < e ∧
      ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β ∧
      ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β ∧
      (a = 0 ∨ b = 0) ∧
      (2 ^ a * w ^ d).factorization 2 = a ∧
      (3 ^ b * v ^ e).factorization 3 = b ∧
      oddPrimeValuationGCD (ordCompl[2] (2 ^ a * w ^ d)) = d ∧
      oddPrimeValuationGCD (ordCompl[3] (3 ^ b * v ^ e)) = e ∧
      simultaneousCoordinateGCD a b d e = 1 := by
  classical
  obtain ⟨w, d, a, c, β, hwodd, hw, hwgcd, hd, hc, haReduced,
      _hindex, _hleast, _hnorm, _hβdef, htwo, hthree, hβirr, hβleast,
      _hsol, _hcand⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  let b : ℕ := c.factorization 3
  let q : ℕ := ordCompl[3] c
  have hqpos : 0 < q := Nat.ordCompl_pos 3 hc.ne'
  have hqneone : q ≠ 1 := by
    intro hqone
    have hcpow : c = 3 ^ b := by
      have hself := Nat.ordProj_mul_ordCompl_eq_self c 3
      change 3 ^ b * q = c at hself
      rw [hqone, mul_one] at hself
      exact hself.symm
    apply hβirr.ne_nat b
    apply (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 3)).injective
    calc
      (3 : ℝ) ^ β = (c : ℝ) := hthree
      _ = ((3 ^ b : ℕ) : ℝ) := by exact_mod_cast hcpow
      _ = (3 : ℝ) ^ (b : ℝ) := by rw [Real.rpow_natCast]; norm_cast
  have hqone : 1 < q := by omega
  obtain ⟨v, e, hv, he, hvprimitive, hqpow⟩ :=
    exists_primitivePowerDecomposition hqone
  have hvthree : ¬ 3 ∣ v := by
    intro hthreev
    have hthreeq : 3 ∣ q := by
      rw [hqpow]
      exact hthreev.trans (dvd_pow_self v he.ne')
    exact (Nat.not_dvd_ordCompl Nat.prime_three hc.ne') hthreeq
  have hcdecomp : c = 3 ^ b * v ^ e := by
    have hself := Nat.ordProj_mul_ordCompl_eq_self c 3
    change 3 ^ b * q = c at hself
    rw [hqpow] at hself
    exact hself.symm
  have hwprimitive : NatPowerPrimitive w :=
    natPowerPrimitive_of_oddPrimeValuationGCD_eq_one hwgcd
  have hvgcd : oddPrimeValuationGCD v = 1 :=
    oddPrimeValuationGCD_eq_one_of_natPowerPrimitive hv hvprimitive
  have hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β := htwo.symm
  have hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β := by
    rw [← hcdecomp]
    exact hthree.symm
  have habzero : a = 0 ∨ b = 0 := by
    rcases haReduced with ha0 | hthreec
    · exact Or.inl ha0
    · right
      by_contra hb0
      apply hthreec
      rw [hcdecomp]
      exact (dvd_pow_self 3 hb0).trans (dvd_mul_right _ _)
  have hMbaseDepth : (2 ^ a * w ^ d).factorization 2 = a := by
    rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
        (pow_ne_zero _ (by omega : w ≠ 0)),
      Nat.factorization_pow, Nat.factorization_pow]
    simp [Finsupp.add_apply, Finsupp.smul_apply,
      (by norm_num : Nat.Prime 2).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hwodd.not_two_dvd_nat]
  have hBbaseDepth : (3 ^ b * v ^ e).factorization 3 = b := by
    rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num : (3 : ℕ) ≠ 0))
        (pow_ne_zero _ (by omega : v ≠ 0)),
      Nat.factorization_pow, Nat.factorization_pow]
    simp [Finsupp.add_apply, Finsupp.smul_apply,
      (by norm_num : Nat.Prime 3).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hvthree]
  have hMdegree :
      oddPrimeValuationGCD (ordCompl[2] (2 ^ a * w ^ d)) = d :=
    valuationGCD_ordCompl_primePower_mul_primitivePower Nat.prime_two
      hwodd.not_two_dvd_nat hwgcd hd
  have hBdegree :
      oddPrimeValuationGCD (ordCompl[3] (3 ^ b * v ^ e)) = e :=
    valuationGCD_ordCompl_primePower_mul_primitivePower Nat.prime_three
      hvthree hvgcd he
  have hsim : simultaneousCoordinateGCD a b d e = 1 :=
    hβleast.simultaneousCoordinateGCD_eq_one hd hM hB
  exact ⟨β, a, b, w, v, d, e, hβirr, hβleast, hwodd, hw,
    hwprimitive, hvthree, hv, hvprimitive, hd, he, hM, hB,
    habzero, hMbaseDepth, hBbaseDepth, hMdegree, hBdegree, hsim⟩

/-- If the exponent is at least `12` and one of the two base-adic depths vanishes,
then the corresponding primitive-power core is already large. -/
theorem primitiveCore_size_dichotomy_of_twelve_le
    {β : ℝ} {a b w v d e : ℕ} (hβ : (12 : ℝ) ≤ β)
    (hM : ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β)
    (hab : a = 0 ∨ b = 0) :
    4096 ≤ w ^ d ∨ 3 ^ 12 ≤ v ^ e := by
  rcases hab with rfl | rfl
  · left
    have hpow : (2 : ℝ) ^ (12 : ℝ) ≤ (2 : ℝ) ^ β :=
      (Real.strictMono_rpow_of_base_gt_one
        (by norm_num : (1 : ℝ) < 2)).monotone hβ
    have hcast : ((4096 : ℕ) : ℝ) ≤ ((w ^ d : ℕ) : ℝ) := by
      calc
        ((4096 : ℕ) : ℝ) = (2 : ℝ) ^ (12 : ℝ) := by
          norm_num [Real.rpow_natCast]
        _ ≤ (2 : ℝ) ^ β := hpow
        _ = ((w ^ d : ℕ) : ℝ) := by simpa using hM.symm
    exact_mod_cast hcast
  · right
    have hpow : (3 : ℝ) ^ (12 : ℝ) ≤ (3 : ℝ) ^ β :=
      (Real.strictMono_rpow_of_base_gt_one
        (by norm_num : (1 : ℝ) < 3)).monotone hβ
    have hcast : (((3 : ℕ) ^ 12 : ℕ) : ℝ) ≤ ((v ^ e : ℕ) : ℝ) := by
      calc
        (((3 : ℕ) ^ 12 : ℕ) : ℝ) = (3 : ℝ) ^ (12 : ℝ) := by
          norm_num [Real.rpow_natCast]
        _ ≤ (3 : ℝ) ^ β := hpow
        _ = ((v ^ e : ℕ) : ℝ) := by simpa using hB.symm
    exact_mod_cast hcast

/-- Under failure, the simultaneous primitive normalization has a large core on at least
one side: the odd core of the base-`2` output is at least `4096`, or the base-`3`-free
core of the base-`3` output is at least `3^12`. -/
theorem exists_large_primitiveCore_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ w v d e : ℕ,
      Odd w ∧ 1 < w ∧ NatPowerPrimitive w ∧
      ¬ 3 ∣ v ∧ 1 < v ∧ NatPowerPrimitive v ∧
      0 < d ∧ 0 < e ∧
      (4096 ≤ w ^ d ∨ 3 ^ 12 ≤ v ^ e) := by
  obtain ⟨β, a, b, w, v, d, e, _hβirr, hβleast, hwodd, hw,
      hwprimitive, hvthree, hv, hvprimitive, hd, he, hM, hB, hab,
      _hMbaseDepth, _hBbaseDepth, _hMdegree, _hBdegree, _hsim⟩ :=
    exists_simultaneous_primitive_output_normalization hfail
  have hβ12 : (12 : ℝ) ≤ β :=
    twelve_le_of_not_integer_of_two_three_rpow_integer
      hβleast.1.1.1 hβleast.1.1.2 hβleast.1.2
  exact ⟨w, v, d, e, hwodd, hw, hwprimitive, hvthree, hv, hvprimitive,
    hd, he, primitiveCore_size_dichotomy_of_twelve_le hβ12 hM hB hab⟩

end

end LeanProofs.TwoBaseIntegerExponent
