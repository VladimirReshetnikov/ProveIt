import ExponentialIdentities.TwoBaseIntegerExponent.RationalSixExponentials
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Rational third bases in the two-base integral-exponent problem

The generic rational six-exponentials determinant is provided upstream by
`RationalSixExponentials`. This module specializes it to the fixed bases `2,3` and
develops the exact arithmetic classification of positive rational third bases.
-/

open scoped BigOperators Nat

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- Rational six-exponentials theorem for a positive rational third base. -/
theorem rational_of_two_three_rat_rpow_rational_of_monomial_injective
    {q : ℚ} (hq : 0 < q)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℚ) ^ u.1 * (3 : ℚ) ^ u.2.1 * q ^ u.2.2))
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (hqPow : ∃ r : ℚ, (r : ℝ) = (q : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  apply RationalSixExponentials.rational_of_three_rat_rpows_rational_of_monomial_injective
      (by norm_num : (0 : ℚ) < 2) (by norm_num : (0 : ℚ) < 3) hq hmono
  · obtain ⟨z, hz⟩ := h₂
    exact ⟨(z : ℚ), by simpa using hz⟩
  · obtain ⟨z, hz⟩ := h₃
    exact ⟨(z : ℚ), by simpa using hz⟩
  · exact hqPow

/-- The rationality conclusion upgrades to integrality using the integral power at `2`. -/
theorem integer_of_two_three_rat_rpow_rational_of_monomial_injective
    {q : ℚ} (hq : 0 < q)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℚ) ^ u.1 * (3 : ℚ) ^ u.2.1 * q ^ u.2.2))
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (hqPow : ∃ r : ℚ, (r : ℝ) = (q : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  apply IntegerExponent.integer_of_rational_of_two_rpow_integer
  · exact rational_of_two_three_rat_rpow_rational_of_monomial_injective
      hq hmono h₂ h₃ hqPow
  · exact h₂

/-- A rational number is a `2,3`-unit when it is a ratio of products of powers of
`2` and `3`. -/
def IsTwoThreeUnit (q : ℚ) : Prop :=
  ∃ i j k l : ℕ,
    q = ((2 ^ i * 3 ^ j : ℕ) : ℚ) / ((2 ^ k * 3 ^ l : ℕ) : ℚ)

private theorem padicValRat_ne_zero_of_prime_dvd_num {q : ℚ} {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ q.num.natAbs) (hq0 : q ≠ 0) :
    padicValRat p q ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnum0 : q.num.natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using Rat.num_ne_zero.mpr hq0
  have hvnum : padicValInt p q.num ≠ 0 := by
    change padicValNat p q.num.natAbs ≠ 0
    exact (dvd_iff_padicValNat_ne_zero hnum0).mp hpq
  have hcop : p.Coprime q.den := q.reduced.of_dvd_left hpq
  have hpden : ¬ p ∣ q.den := hp.coprime_iff_not_dvd.mp hcop
  have hvden : padicValNat p q.den = 0 :=
    padicValNat.eq_zero_of_not_dvd hpden
  rw [padicValRat_def, hvden]
  simp only [Nat.cast_zero, sub_zero]
  exact_mod_cast hvnum

private theorem padicValRat_ne_zero_of_prime_dvd_den {q : ℚ} {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ q.den) :
    padicValRat p q ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hvden : padicValNat p q.den ≠ 0 :=
    (dvd_iff_padicValNat_ne_zero q.den_nz).mp hpq
  have hcop : p.Coprime q.num.natAbs := q.reduced.symm.of_dvd_left hpq
  have hpnum : ¬ p ∣ q.num.natAbs := hp.coprime_iff_not_dvd.mp hcop
  have hvnum : padicValInt p q.num = 0 := by
    change padicValNat p q.num.natAbs = 0
    exact padicValNat.eq_zero_of_not_dvd hpnum
  rw [padicValRat_def, hvnum, Nat.cast_zero, zero_sub, neg_ne_zero]
  exact_mod_cast hvden

private theorem rational_monomial_injective_of_padicVal_ne_zero
    {q : ℚ} (hq0 : q ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : padicValRat p q ≠ 0) :
    Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℚ) ^ u.1 * (3 : ℚ) ^ u.2.1 * q ^ u.2.2) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpnot2 : ¬ p ∣ 2 := by
    intro h
    exact hp2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hp.ne_one)
  have hpnot3 : ¬ p ∣ 3 := by
    intro h
    exact hp3 (((Nat.dvd_prime Nat.prime_three).mp h).resolve_left hp.ne_one)
  have hval2 : padicValRat p (2 : ℚ) = 0 := by
    change (padicValNat p 2 : ℤ) - (padicValNat p 1 : ℤ) = 0
    rw [padicValNat.eq_zero_of_not_dvd hpnot2]
    simp
  have hval3 : padicValRat p (3 : ℚ) = 0 := by
    change (padicValNat p 3 : ℤ) - (padicValNat p 1 : ℤ) = 0
    rw [padicValNat.eq_zero_of_not_dvd hpnot3]
    simp
  have hval (i j k : ℕ) :
      padicValRat p ((2 : ℚ) ^ i * (3 : ℚ) ^ j * q ^ k) =
        (k : ℤ) * padicValRat p q := by
    rw [padicValRat.mul
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
        (pow_ne_zero _ hq0),
      padicValRat.mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))]
    simp [hval2, hval3]
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have hv := congrArg (padicValRat p) h
  rw [hval, hval] at hv
  have hkZ : (k : ℤ) = (k' : ℤ) := mul_right_cancel₀ hpq hv
  have hk : k = k' := by exact_mod_cast hkZ
  subst k'
  have h23Q : (2 : ℚ) ^ i * (3 : ℚ) ^ j =
      (2 : ℚ) ^ i' * (3 : ℚ) ^ j' := by
    exact mul_right_cancel₀ (pow_ne_zero k hq0) h
  have h23 : 2 ^ i * 3 ^ j = 2 ^ i' * 3 ^ j' := by
    exact_mod_cast h23Q
  have hinj := monomial_injective_of_prime_dvd_ne_two_three
    (a := 5) (p := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have huv := hinj
    (a₁ := ((i, j, 0) : ℕ × ℕ × ℕ))
    (a₂ := ((i', j', 0) : ℕ × ℕ × ℕ)) (by simpa using h23)
  simpa only [Prod.mk.injEq] using huv

private theorem isTwoThreeUnit_of_num_den_smooth {q : ℚ} (hqpos : 0 < q)
    (hnum : ∀ p : ℕ, p.Prime → p ∣ q.num.natAbs → p = 2 ∨ p = 3)
    (hden : ∀ p : ℕ, p.Prime → p ∣ q.den → p = 2 ∨ p = 3) :
    IsTwoThreeUnit q := by
  have hnumposZ : 0 < q.num := Rat.num_pos.mpr hqpos
  have hnumpos : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnumposZ.ne'
  obtain ⟨i, j, hnumEq⟩ :=
    (Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hnumpos).mp hnum
  obtain ⟨k, l, hdenEq⟩ :=
    (Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow q.den_pos).mp hden
  refine ⟨i, j, k, l, ?_⟩
  have hnumcast : (q.num.natAbs : ℤ) = q.num :=
    Int.natAbs_of_nonneg hnumposZ.le
  have hnumInt : q.num = (2 ^ i * 3 ^ j : ℕ) := by
    rw [← hnumcast]
    exact_mod_cast hnumEq
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_def q, Rat.cast_div]
  push_cast
  rw [hnumInt, hdenEq]
  congr 1 <;> norm_cast

private theorem exists_prime_padicValRat_ne_zero_of_not_isTwoThreeUnit
    {q : ℚ} (hqpos : 0 < q) (hnot : ¬ IsTwoThreeUnit q) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ padicValRat p q ≠ 0 := by
  have hq0 : q ≠ 0 := ne_of_gt hqpos
  by_cases hnum : ∀ p : ℕ, p.Prime → p ∣ q.num.natAbs → p = 2 ∨ p = 3
  · by_cases hden : ∀ p : ℕ, p.Prime → p ∣ q.den → p = 2 ∨ p = 3
    · exact (hnot (isTwoThreeUnit_of_num_den_smooth hqpos hnum hden)).elim
    · push Not at hden
      obtain ⟨p, hp, hpd, hp2, hp3⟩ := hden
      exact ⟨p, hp, hp2, hp3, padicValRat_ne_zero_of_prime_dvd_den hp hpd⟩
  · push Not at hnum
    obtain ⟨p, hp, hpd, hp2, hp3⟩ := hnum
    exact ⟨p, hp, hp2, hp3,
      padicValRat_ne_zero_of_prime_dvd_num hp hpd hq0⟩

/-- A positive rational not generated by `2` and `3` supplies an injective third
monomial coordinate. -/
theorem rational_monomial_injective_of_not_isTwoThreeUnit
    {q : ℚ} (hqpos : 0 < q) (hnot : ¬ IsTwoThreeUnit q) :
    Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℚ) ^ u.1 * (3 : ℚ) ^ u.2.1 * q ^ u.2.2) := by
  obtain ⟨p, hp, hp2, hp3, hpq⟩ :=
    exists_prime_padicValRat_ne_zero_of_not_isTwoThreeUnit hqpos hnot
  exact rational_monomial_injective_of_padicVal_ne_zero
    (ne_of_gt hqpos) hp hp2 hp3 hpq

/-- Under a nonintegral exponent with integral powers at `2` and `3`, a positive rational
base has rational `x`-th power exactly when it is a ratio of `2,3`-smooth naturals. -/
theorem rat_rpow_rational_iff_isTwoThreeUnit_of_not_integer
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    {q : ℚ} (hq : 0 < q) :
    (∃ r : ℚ, (r : ℝ) = (q : ℝ) ^ x) ↔ IsTwoThreeUnit q := by
  constructor
  · intro hqPow
    by_contra hnot
    exact hx (integer_of_two_three_rat_rpow_rational_of_monomial_injective
      hq (rational_monomial_injective_of_not_isTwoThreeUnit hq hnot)
      h₂ h₃ hqPow)
  · rintro ⟨i, j, k, l, hqrep⟩
    obtain ⟨z₂, hz₂⟩ := h₂
    obtain ⟨z₃, hz₃⟩ := h₃
    refine ⟨(((z₂ ^ i * z₃ ^ j : ℤ) : ℚ) /
      ((z₂ ^ k * z₃ ^ l : ℤ) : ℚ)), ?_⟩
    rw [Rat.cast_div]
    push_cast
    rw [hqrep, Rat.cast_div]
    push_cast
    rw [Real.div_rpow (by positivity) (by positivity)]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x i,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x j,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x k,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x l]
    rw [← hz₂, ← hz₃]

/-- Expanded four-natural-exponent form of the exact rational-base classification. -/
theorem rat_rpow_rational_iff_eq_two_three_ratio_of_not_integer
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    {q : ℚ} (hq : 0 < q) :
    (∃ r : ℚ, (r : ℝ) = (q : ℝ) ^ x) ↔
      ∃ i j k l : ℕ,
        q = ((2 ^ i * 3 ^ j : ℕ) : ℚ) /
          ((2 ^ k * 3 ^ l : ℕ) : ℚ) := by
  simpa only [IsTwoThreeUnit] using
    rat_rpow_rational_iff_isTwoThreeUnit_of_not_integer hx h₂ h₃ hq

/-- Predicate-packaged version for a nonintegral two-base solution. -/
theorem twoBaseNonintegerSolution_rat_rpow_rational_iff_ratio
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {q : ℚ} (hq : 0 < q) :
    (∃ r : ℚ, (r : ℝ) = (q : ℝ) ^ x) ↔
      ∃ i j k l : ℕ,
        q = ((2 ^ i * 3 ^ j : ℕ) : ℚ) /
          ((2 ^ k * 3 ^ l : ℕ) : ℚ) :=
  rat_rpow_rational_iff_eq_two_three_ratio_of_not_integer
    hx.2 hx.1.1 hx.1.2 hq

end

end LeanProofs.TwoBaseIntegerExponent
