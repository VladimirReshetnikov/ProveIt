import ExponentialIdentities.TwoBaseIntegerExponent.OutputNormalization
import ExponentialIdentities.TwoBaseIntegerExponent.Transcendence
import ExponentialIdentities.TwoBaseIntegerExponent.RationalThirdBase

open scoped Nat

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

/-- The two primitive cores in a simultaneous normalization cannot be exactly `3` and `2`.
Such a normalization would make `log 3 / log 2` satisfy a nonzero quadratic over `ℚ`. -/
theorem not_simultaneous_three_two_output_cores
    {β : ℝ} {a b d e : ℕ} (hd : 0 < d)
    (hM : ((2 ^ a * 3 ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β)
    (hB : ((3 ^ b * 2 ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β) : False := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hMlog :
      (a : ℝ) * Real.log 2 + (d : ℝ) * Real.log 3 = β * Real.log 2 := by
    have h := congrArg Real.log hM
    push_cast at h
    rw [Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
        (pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)),
      Real.log_pow, Real.log_pow,
      Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at h
    exact h
  have hBlog :
      (b : ℝ) * Real.log 3 + (e : ℝ) * Real.log 2 = β * Real.log 3 := by
    have h := congrArg Real.log hB
    push_cast at h
    rw [Real.log_mul (pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0))
        (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      Real.log_pow, Real.log_pow,
      Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at h
    exact h
  have hMmul := congrArg (fun z : ℝ => z * Real.log 3) hMlog
  have hBmul := congrArg (fun z : ℝ => z * Real.log 2) hBlog
  have hquad :
      (d : ℝ) * logThreeDivLogTwo ^ 2 +
          ((a : ℝ) - (b : ℝ)) * logThreeDivLogTwo - (e : ℝ) = 0 := by
    rw [logThreeDivLogTwo]
    field_simp
    nlinarith
  let P : Polynomial ℚ :=
    Polynomial.C (d : ℚ) * Polynomial.X ^ 2 +
      Polynomial.C ((a : ℚ) - (b : ℚ)) * Polynomial.X - Polynomial.C (e : ℚ)
  have hPne : P ≠ 0 := by
    intro hP
    have hcoeff := congrArg (fun Q : Polynomial ℚ => Q.coeff 2) hP
    simp [P] at hcoeff
    exact hd.ne' (by exact_mod_cast hcoeff)
  have hPeval : Polynomial.aeval logThreeDivLogTwo P = 0 := by
    simpa [P] using hquad
  exact transcendental_logThreeDivLogTwo ⟨P, hPne, hPeval⟩

/-- For a nonintegral two-base solution, the two first iterates of its integral
outputs cannot both be rational. -/
theorem TwoBaseNonintegerSolution.not_both_iterated_outputs_rational
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ¬ ((∃ q : ℚ, (q : ℝ) = ((2 : ℝ) ^ x) ^ x) ∧
      ∃ q : ℚ, (q : ℝ) = ((3 : ℝ) ^ x) ^ x) := by
  rintro ⟨hiterTwo, hiterThree⟩
  obtain ⟨zTwo, hzTwo⟩ := hx.1.1
  obtain ⟨zThree, hzThree⟩ := hx.1.2
  have hzTwoPos : 0 < zTwo := by
    exact_mod_cast (hzTwo.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
  have hzThreePos : 0 < zThree := by
    exact_mod_cast (hzThree.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) x)
  let M : ℕ := zTwo.natAbs
  let B : ℕ := zThree.natAbs
  have hMpos : 0 < M := by
    exact Int.natAbs_pos.mpr hzTwoPos.ne'
  have hBpos : 0 < B := by
    exact Int.natAbs_pos.mpr hzThreePos.ne'
  have hM : (M : ℝ) = (2 : ℝ) ^ x := by
    calc
      (M : ℝ) = (zTwo : ℝ) := by
        exact_mod_cast (show (M : ℤ) = zTwo by
          simpa [M] using Int.natAbs_of_nonneg hzTwoPos.le)
      _ = (2 : ℝ) ^ x := hzTwo
  have hB : (B : ℝ) = (3 : ℝ) ^ x := by
    calc
      (B : ℝ) = (zThree : ℝ) := by
        exact_mod_cast (show (B : ℤ) = zThree by
          simpa [B] using Int.natAbs_of_nonneg hzThreePos.le)
      _ = (3 : ℝ) ^ x := hzThree
  have hMrat : ∃ q : ℚ, (q : ℝ) = (M : ℝ) ^ x := by
    simpa only [hM] using hiterTwo
  have hBrat : ∃ q : ℚ, (q : ℝ) = (B : ℝ) ^ x := by
    simpa only [hB] using hiterThree
  obtain ⟨a, d, hMdecomp⟩ :=
    (hx.rpow_rational_iff_eq_two_pow_mul_three_pow hMpos).mp hMrat
  obtain ⟨e, b, hBdecomp⟩ :=
    (hx.rpow_rational_iff_eq_two_pow_mul_three_pow hBpos).mp hBrat
  have hd : 0 < d := by
    by_contra hd
    have hdZero : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    apply hx.2
    refine ⟨(a : ℤ), ?_⟩
    have hxEq : x = (a : ℝ) := by
      apply (Real.strictMono_rpow_of_base_gt_one
        (by norm_num : (1 : ℝ) < 2)).injective
      calc
        (2 : ℝ) ^ x = (M : ℝ) := hM.symm
        _ = ((2 ^ a : ℕ) : ℝ) := by
          simpa using congrArg ((↑) : ℕ → ℝ) hMdecomp
        _ = (2 : ℝ) ^ (a : ℝ) := by rw [Real.rpow_natCast]; norm_cast
    exact_mod_cast hxEq.symm
  have hMcore : ((2 ^ a * 3 ^ d : ℕ) : ℝ) = (2 : ℝ) ^ x := by
    rw [← hMdecomp]
    exact hM
  have hBcore : ((3 ^ b * 2 ^ e : ℕ) : ℝ) = (3 : ℝ) ^ x := by
    rw [mul_comm, ← hBdecomp]
    exact hB
  exact not_simultaneous_three_two_output_cores hd hMcore hBcore

/-- An odd, power-primitive number other than `3` has a prime divisor outside `2,3`. -/
theorem exists_prime_ne_two_three_of_odd_primitive_ne_three
    {w : ℕ} (hwodd : Odd w) (hw : 1 < w) (hprimitive : NatPowerPrimitive w)
    (hw3 : w ≠ 3) :
    ∃ p : ℕ, p.Prime ∧ p ∣ w ∧ p ≠ 2 ∧ p ≠ 3 := by
  by_contra hnone
  have hall : ∀ p : ℕ, p.Prime → p ∣ w → p = 2 ∨ p = 3 := by
    intro p hp hpd
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    by_cases hp3 : p = 3
    · exact Or.inr hp3
    exact (hnone ⟨p, hp, hpd, hp2, hp3⟩).elim
  obtain ⟨u, t, hwt⟩ :=
    (Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow
      (Nat.zero_lt_one.trans hw)).mp hall
  have hu : u = 0 := by
    by_contra hu0
    have htwo : 2 ∣ w := by
      rw [hwt]
      exact (dvd_pow_self 2 hu0).trans (dvd_mul_right _ _)
    exact hwodd.not_two_dvd_nat htwo
  simp only [hu, pow_zero, one_mul] at hwt
  have ht : t = 1 := by
    by_contra ht1
    have ht2 : 2 ≤ t := by
      have ht0 : t ≠ 0 := by
        intro ht0
        rw [ht0, pow_zero] at hwt
        omega
      omega
    exact hprimitive 3 t (by norm_num) ht2 hwt
  exact hw3 (by simpa [ht] using hwt)

/-- A power-primitive number not divisible by `3`, other than `2`, has a prime divisor
outside `2,3`. -/
theorem exists_prime_ne_two_three_of_three_free_primitive_ne_two
    {v : ℕ} (hvthree : ¬ 3 ∣ v) (hv : 1 < v) (hprimitive : NatPowerPrimitive v)
    (hv2 : v ≠ 2) :
    ∃ p : ℕ, p.Prime ∧ p ∣ v ∧ p ≠ 2 ∧ p ≠ 3 := by
  by_contra hnone
  have hall : ∀ p : ℕ, p.Prime → p ∣ v → p = 2 ∨ p = 3 := by
    intro p hp hpd
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    by_cases hp3 : p = 3
    · exact Or.inr hp3
    exact (hnone ⟨p, hp, hpd, hp2, hp3⟩).elim
  obtain ⟨u, t, hvt⟩ :=
    (Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow
      (Nat.zero_lt_one.trans hv)).mp hall
  have ht : t = 0 := by
    by_contra ht0
    apply hvthree
    rw [hvt]
    exact (dvd_pow_self 3 ht0).trans (dvd_mul_left _ _)
  simp only [ht, pow_zero, mul_one] at hvt
  have hu : u = 1 := by
    by_contra hu1
    have hu2 : 2 ≤ u := by
      have hu0 : u ≠ 0 := by
        intro hu0
        rw [hu0, pow_zero] at hvt
        omega
      omega
    exact hprimitive 2 u (by norm_num) hu2 hvt
  exact hv2 (by simpa [hu] using hvt)

/-- For an odd primitive core of a nonintegral two-base solution, rationality of its
`x`-th power is equivalent to the sole smooth possibility `w = 3`. -/
theorem TwoBaseNonintegerSolution.rpow_rational_iff_eq_three_of_odd_primitive
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {w : ℕ} (hwodd : Odd w) (hw : 1 < w) (hprimitive : NatPowerPrimitive w) :
    (∃ q : ℚ, (q : ℝ) = (w : ℝ) ^ x) ↔ w = 3 := by
  constructor
  · intro hrat
    obtain ⟨u, t, hwt⟩ :=
      (hx.rpow_rational_iff_eq_two_pow_mul_three_pow
        (Nat.zero_lt_one.trans hw)).mp hrat
    have hu : u = 0 := by
      by_contra hu0
      have htwo : 2 ∣ w := by
        rw [hwt]
        exact (dvd_pow_self 2 hu0).trans (dvd_mul_right _ _)
      exact hwodd.not_two_dvd_nat htwo
    simp only [hu, pow_zero, one_mul] at hwt
    have ht : t = 1 := by
      by_contra ht1
      have ht2 : 2 ≤ t := by
        have ht0 : t ≠ 0 := by
          intro ht0
          rw [ht0, pow_zero] at hwt
          omega
        omega
      exact hprimitive 3 t (by norm_num) ht2 hwt
    simpa [ht] using hwt
  · rintro rfl
    obtain ⟨z, hz⟩ := hx.1.2
    exact ⟨(z : ℚ), by simpa using hz⟩

/-- For a `3`-free primitive core of a nonintegral two-base solution, rationality of its
`x`-th power is equivalent to the sole smooth possibility `v = 2`. -/
theorem TwoBaseNonintegerSolution.rpow_rational_iff_eq_two_of_three_free_primitive
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {v : ℕ} (hvthree : ¬ 3 ∣ v) (hv : 1 < v) (hprimitive : NatPowerPrimitive v) :
    (∃ q : ℚ, (q : ℝ) = (v : ℝ) ^ x) ↔ v = 2 := by
  constructor
  · intro hrat
    obtain ⟨u, t, hvt⟩ :=
      (hx.rpow_rational_iff_eq_two_pow_mul_three_pow
        (Nat.zero_lt_one.trans hv)).mp hrat
    have ht : t = 0 := by
      by_contra ht0
      apply hvthree
      rw [hvt]
      exact (dvd_pow_self 3 ht0).trans (dvd_mul_left _ _)
    simp only [ht, pow_zero, mul_one] at hvt
    have hu : u = 1 := by
      by_contra hu1
      have hu2 : 2 ≤ u := by
        have hu0 : u ≠ 0 := by
          intro hu0
          rw [hu0, pow_zero] at hvt
          omega
        omega
      exact hprimitive 2 u (by norm_num) hu2 hvt
    simpa [hu] using hvt
  · rintro rfl
    obtain ⟨z, hz⟩ := hx.1.1
    exact ⟨(z : ℚ), by simpa using hz⟩

/-- Under failure, at least one of the two canonical primitive output cores has a prime
divisor genuinely outside the distinguished bases `2` and `3`. -/
theorem exists_external_prime_in_simultaneous_primitive_output_cores
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ, ∃ a b w v d e : ℕ,
      Irrational β ∧ IsLeastTwoBaseNonintegerSolution β ∧
      Odd w ∧ 1 < w ∧ NatPowerPrimitive w ∧
      ¬ 3 ∣ v ∧ 1 < v ∧ NatPowerPrimitive v ∧
      0 < d ∧ 0 < e ∧
      ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β ∧
      ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β ∧
      (a = 0 ∨ b = 0) ∧
      ((∃ p : ℕ, p.Prime ∧ p ∣ w ∧ p ≠ 2 ∧ p ≠ 3) ∨
        ∃ p : ℕ, p.Prime ∧ p ∣ v ∧ p ≠ 2 ∧ p ≠ 3) := by
  obtain ⟨β, a, b, w, v, d, e, hβirr, hβleast, hwodd, hw,
      hwprimitive, hvthree, hv, hvprimitive, hd, he, hM, hB, hab,
      _hMdepth, _hBdepth, _hMdegree, _hBdegree, _hgcd⟩ :=
    exists_simultaneous_primitive_output_normalization hfail
  have hne : w ≠ 3 ∨ v ≠ 2 := by
    by_contra hboth
    push Not at hboth
    rcases hboth with ⟨rfl, rfl⟩
    exact not_simultaneous_three_two_output_cores hd hM hB
  refine ⟨β, a, b, w, v, d, e, hβirr, hβleast, hwodd, hw, hwprimitive,
    hvthree, hv, hvprimitive, hd, he, hM, hB, hab, ?_⟩
  rcases hne with hw3 | hv2
  · exact Or.inl
      (exists_prime_ne_two_three_of_odd_primitive_ne_three hwodd hw hwprimitive hw3)
  · exact Or.inr
      (exists_prime_ne_two_three_of_three_free_primitive_ne_two hvthree hv hvprimitive hv2)

/-- The two canonical primitive cores have completely determined rational-power behavior:
the odd core has rational `β`-th power exactly when it is `3`, the `3`-free core has
rational `β`-th power exactly when it is `2`, and these cases cannot occur together. -/
theorem exists_exact_rationality_classification_of_simultaneous_cores
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ, ∃ a b w v d e : ℕ,
      Irrational β ∧ IsLeastTwoBaseNonintegerSolution β ∧
      Odd w ∧ 1 < w ∧ NatPowerPrimitive w ∧
      ¬ 3 ∣ v ∧ 1 < v ∧ NatPowerPrimitive v ∧
      0 < d ∧ 0 < e ∧
      ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β ∧
      ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β ∧
      (a = 0 ∨ b = 0) ∧
      ((∃ q : ℚ, (q : ℝ) = (w : ℝ) ^ β) ↔ w = 3) ∧
      ((∃ q : ℚ, (q : ℝ) = (v : ℝ) ^ β) ↔ v = 2) ∧
      ¬ ((∃ q : ℚ, (q : ℝ) = (w : ℝ) ^ β) ∧
        ∃ q : ℚ, (q : ℝ) = (v : ℝ) ^ β) := by
  obtain ⟨β, a, b, w, v, d, e, hβirr, hβleast, hwodd, hw,
      hwprimitive, hvthree, hv, hvprimitive, hd, he, hM, hB, hab,
      _hMdepth, _hBdepth, _hMdegree, _hBdegree, _hgcd⟩ :=
    exists_simultaneous_primitive_output_normalization hfail
  have hwrat :=
    hβleast.1.rpow_rational_iff_eq_three_of_odd_primitive hwodd hw hwprimitive
  have hvrat :=
    hβleast.1.rpow_rational_iff_eq_two_of_three_free_primitive
      hvthree hv hvprimitive
  have hnotboth :
      ¬ ((∃ q : ℚ, (q : ℝ) = (w : ℝ) ^ β) ∧
        ∃ q : ℚ, (q : ℝ) = (v : ℝ) ^ β) := by
    rintro ⟨hwq, hvq⟩
    have hw3 : w = 3 := hwrat.mp hwq
    have hv2 : v = 2 := hvrat.mp hvq
    subst w
    subst v
    exact not_simultaneous_three_two_output_cores hd hM hB
  exact ⟨β, a, b, w, v, d, e, hβirr, hβleast, hwodd, hw, hwprimitive,
    hvthree, hv, hvprimitive, hd, he, hM, hB, hab, hwrat, hvrat, hnotboth⟩

/-- A nonintegral two-base solution has an irrational power at every natural base carrying
a prime factor outside `2,3`. -/
theorem TwoBaseNonintegerSolution.not_rpow_rational_of_prime_factor_ne_two_three
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {a p : ℕ} (ha : 0 < a) (hp : p.Prime) (hpa : p ∣ a)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ ∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x := by
  intro haPow
  exact hx.2 (integer_of_two_three_a_rpow_rational_of_prime_factor
    ha hp hpa hp2 hp3 hx.1.1 hx.1.2 haPow)

/-- Under failure, at least one of the two canonical primitive cores has irrational
`β`-th power, where `β` is the least nonintegral solution. -/
theorem exists_irrational_canonical_core_power_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ, ∃ a b w v d e : ℕ,
      Irrational β ∧ IsLeastTwoBaseNonintegerSolution β ∧
      Odd w ∧ 1 < w ∧ NatPowerPrimitive w ∧
      ¬ 3 ∣ v ∧ 1 < v ∧ NatPowerPrimitive v ∧
      0 < d ∧ 0 < e ∧
      ((2 ^ a * w ^ d : ℕ) : ℝ) = (2 : ℝ) ^ β ∧
      ((3 ^ b * v ^ e : ℕ) : ℝ) = (3 : ℝ) ^ β ∧
      (a = 0 ∨ b = 0) ∧
      ((¬ ∃ q : ℚ, (q : ℝ) = (w : ℝ) ^ β) ∨
        ¬ ∃ q : ℚ, (q : ℝ) = (v : ℝ) ^ β) := by
  obtain ⟨β, a, b, w, v, d, e, hβirr, hβleast, hwodd, hw,
      hwprimitive, hvthree, hv, hvprimitive, hd, he, hM, hB, hab,
      _hMdepth, _hBdepth, _hMdegree, _hBdegree, _hgcd⟩ :=
    exists_simultaneous_primitive_output_normalization hfail
  have hne : w ≠ 3 ∨ v ≠ 2 := by
    by_contra hboth
    push Not at hboth
    rcases hboth with ⟨rfl, rfl⟩
    exact not_simultaneous_three_two_output_cores hd hM hB
  refine ⟨β, a, b, w, v, d, e, hβirr, hβleast, hwodd, hw, hwprimitive,
    hvthree, hv, hvprimitive, hd, he, hM, hB, hab, ?_⟩
  rcases hne with hw3 | hv2
  · obtain ⟨p, hp, hpw, hp2, hp3⟩ :=
      exists_prime_ne_two_three_of_odd_primitive_ne_three hwodd hw hwprimitive hw3
    exact Or.inl
      (hβleast.1.not_rpow_rational_of_prime_factor_ne_two_three
        (Nat.zero_lt_one.trans hw) hp hpw hp2 hp3)
  · obtain ⟨p, hp, hpv, hp2, hp3⟩ :=
      exists_prime_ne_two_three_of_three_free_primitive_ne_two
        hvthree hv hvprimitive hv2
    exact Or.inr
      (hβleast.1.not_rpow_rational_of_prime_factor_ne_two_three
        (Nat.zero_lt_one.trans hv) hp hpv hp2 hp3)

end

end LeanProofs.TwoBaseIntegerExponent
