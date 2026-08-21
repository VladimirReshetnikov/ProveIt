import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicRationalBase
import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicSixExponentials

/-!
# Multiplicative rank of a positive algebraic auxiliary base

This file isolates the arithmetic equivalence needed to turn an algebraic-base
six-exponentials theorem into an exact output classification.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- A positive real has a positive `2,3`-unit power when some positive natural power
is a positive rational generated multiplicatively by `2` and `3`. -/
def HasPositiveTwoThreeUnitPower (gamma : ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ q : ℚ,
    0 < q ∧ IsTwoThreeUnit q ∧ gamma ^ n = (q : ℝ)

private theorem two_three_real_monomial_injective :
    Function.Injective
      (fun u : ℕ × ℕ ↦ (2 : ℝ) ^ u.1 * (3 : ℝ) ^ u.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hnat : 2 ^ i * 3 ^ j = 2 ^ i' * 3 ^ j' := by
    have hcast : ((2 ^ i * 3 ^ j : ℕ) : ℝ) =
        ((2 ^ i' * 3 ^ j' : ℕ) : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      exact h
    exact_mod_cast hcast
  have hinj := monomial_injective_of_prime_dvd_ne_two_three
    (a := 5) (p := 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have huv := hinj
    (a₁ := ((i, j, 0) : ℕ × ℕ × ℕ))
    (a₂ := ((i', j', 0) : ℕ × ℕ × ℕ)) (by simpa using hnat)
  rcases huv with ⟨rfl, rfl, _⟩
  rfl

private theorem collision_of_positive_twoThreeUnitPower
    {gamma : ℝ} (hpow : HasPositiveTwoThreeUnitPower gamma) :
    ¬ Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦
        (2 : ℝ) ^ u.1 * (3 : ℝ) ^ u.2.1 * gamma ^ u.2.2) := by
  rintro hinj
  obtain ⟨n, hn, q, _hqpos, ⟨i, j, k, l, hq⟩, hgammaPow⟩ := hpow
  have hqcast := congrArg (fun r : ℚ ↦ (r : ℝ)) hq
  norm_num only [Rat.cast_div, Rat.cast_natCast, Nat.cast_mul, Nat.cast_pow] at hqcast
  have hden : (0 : ℝ) < (2 : ℝ) ^ k * (3 : ℝ) ^ l := by positivity
  have hcollision :
      (2 : ℝ) ^ k * (3 : ℝ) ^ l * gamma ^ n =
        (2 : ℝ) ^ i * (3 : ℝ) ^ j * gamma ^ 0 := by
    rw [pow_zero, mul_one, hgammaPow, hqcast]
    field_simp
    push_cast
    ring
  have htuple := hinj
    (a₁ := ((k, l, n) : ℕ × ℕ × ℕ))
    (a₂ := ((i, j, 0) : ℕ × ℕ × ℕ)) hcollision
  have : n = 0 := congrArg (fun u : ℕ × ℕ × ℕ ↦ u.2.2) htuple
  omega

private theorem positive_twoThreeUnitPower_of_collision_lt
    {gamma : ℝ} (hgamma : 0 < gamma)
    {i j k i' j' k' : ℕ} (hkk' : k < k')
    (hcollision :
      (2 : ℝ) ^ i * (3 : ℝ) ^ j * gamma ^ k =
        (2 : ℝ) ^ i' * (3 : ℝ) ^ j' * gamma ^ k') :
    HasPositiveTwoThreeUnitPower gamma := by
  let A : ℕ := 2 ^ i * 3 ^ j
  let B : ℕ := 2 ^ i' * 3 ^ j'
  let n : ℕ := k' - k
  have hn : 0 < n := Nat.sub_pos_of_lt hkk'
  have hk' : k' = k + n := by
    dsimp only [n]
    omega
  have hcancel : (A : ℝ) = (B : ℝ) * gamma ^ n := by
    apply mul_right_cancel₀ (pow_ne_zero k hgamma.ne')
    calc
      (A : ℝ) * gamma ^ k =
          (2 : ℝ) ^ i * (3 : ℝ) ^ j * gamma ^ k := by
            norm_num [A]
      _ = (2 : ℝ) ^ i' * (3 : ℝ) ^ j' * gamma ^ k' := hcollision
      _ = (B : ℝ) * gamma ^ (k + n) := by rw [hk']; norm_num [B]
      _ = ((B : ℝ) * gamma ^ n) * gamma ^ k := by
        rw [pow_add]
        ring
  let q : ℚ := (A : ℚ) / (B : ℚ)
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hqpos : 0 < q := by dsimp only [q]; positivity
  have hunit : IsTwoThreeUnit q := by
    refine ⟨i, j, i', j', ?_⟩
    dsimp only [q, A, B]
  have hpow : gamma ^ n = (q : ℝ) := by
    have hBne : (B : ℝ) ≠ 0 := by positivity
    rw [show (q : ℝ) = (A : ℝ) / (B : ℝ) by
      dsimp only [q]
      norm_num]
    apply (eq_div_iff hBne).2
    rw [mul_comm, ← hcancel]
  exact ⟨n, hn, q, hqpos, hunit, hpow⟩

/-- The nonnegative monomials in `2`, `3`, and a positive real `gamma` are injective
exactly when no positive natural power of `gamma` is a positive rational `2,3`-unit. -/
theorem real_two_three_gamma_monomial_injective_iff
    {gamma : ℝ} (hgamma : 0 < gamma) :
    Function.Injective
        (fun u : ℕ × ℕ × ℕ ↦
          (2 : ℝ) ^ u.1 * (3 : ℝ) ^ u.2.1 * gamma ^ u.2.2) ↔
      ¬ HasPositiveTwoThreeUnitPower gamma := by
  constructor
  · intro hinj hpow
    exact collision_of_positive_twoThreeUnitPower hpow hinj
  · intro hno
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hcollision
    by_cases hkk' : k = k'
    · subst k'
      have hbase :
          (2 : ℝ) ^ i * (3 : ℝ) ^ j =
            (2 : ℝ) ^ i' * (3 : ℝ) ^ j' := by
        apply mul_right_cancel₀ (pow_ne_zero k hgamma.ne')
        exact hcollision
      have hij : (i, j) = (i', j') := two_three_real_monomial_injective hbase
      cases hij
      rfl
    · rcases lt_or_gt_of_ne hkk' with hlt | hgt
      · exact (hno (positive_twoThreeUnitPower_of_collision_lt
          hgamma hlt hcollision)).elim
      · exact (hno (positive_twoThreeUnitPower_of_collision_lt
          hgamma hgt hcollision.symm)).elim

private theorem real_rpow_isAlgebraic_of_integer_exponent
    {gamma x : ℝ} (hgammaAlg : IsAlgebraic ℚ gamma)
    (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) :
    IsAlgebraic ℚ (gamma ^ x) := by
  obtain ⟨z, rfl⟩ := hx
  rw [Real.rpow_intCast]
  cases z with
  | ofNat n => simpa using hgammaAlg.pow n
  | negSucc n =>
      rw [zpow_negSucc]
      exact (hgammaAlg.pow (n + 1)).inv

/-- Under a hypothetical nonintegral two-base solution, a positive algebraic base
has algebraic `x`-th power exactly when one of its positive natural powers is a
positive rational `2,3`-unit. -/
theorem TwoBaseNonintegerSolution.real_rpow_isAlgebraic_iff_hasPositiveTwoThreeUnitPower
    {x gamma : ℝ} (hx : TwoBaseNonintegerSolution x)
    (hgamma : 0 < gamma) (hgammaAlg : IsAlgebraic ℚ gamma) :
    IsAlgebraic ℚ (gamma ^ x) ↔ HasPositiveTwoThreeUnitPower gamma := by
  constructor
  · intro hgammaPowAlg
    by_contra hno
    have htwoPowAlg : IsAlgebraic ℚ ((2 : ℝ) ^ x) := by
      obtain ⟨z, hz⟩ := hx.1.1
      rw [← hz]
      exact isAlgebraic_int z
    have hthreePowAlg : IsAlgebraic ℚ ((3 : ℝ) ^ x) := by
      obtain ⟨z, hz⟩ := hx.1.2
      rw [← hz]
      exact isAlgebraic_int z
    have hxrat : x ∈ Set.range ((↑) : ℚ → ℝ) :=
      LeanProofs.AlgebraicSixExponentials.rational_of_three_real_rpows_isAlgebraic_of_monomial_injective
          (a := (2 : ℝ)) (b := (3 : ℝ)) (c := gamma)
          (by norm_num) (by norm_num) hgamma
          (isAlgebraic_nat 2) (isAlgebraic_nat 3) hgammaAlg
          ((real_two_three_gamma_monomial_injective_iff hgamma).2 hno)
          htwoPowAlg hthreePowAlg hgammaPowAlg
    exact hx.2
      (LeanProofs.IntegerExponent.integer_of_rational_of_two_rpow_integer
        hxrat hx.1.1)
  · rintro ⟨n, hn, q, hq, hunit, hgammaPow⟩
    apply IsAlgebraic.of_pow hn
    rw [Real.rpow_pow_comm hgamma.le x n, hgammaPow]
    exact rpow_isAlgebraic_of_isTwoThreeUnit hx hq hunit

/-- Pointwise classification without a nonintegrality assumption.  Under the two
integrality hypotheses, an algebraic output at a positive algebraic base comes
exactly from an integral exponent or from a positive `2,3`-unit power of the base. -/
theorem real_rpow_isAlgebraic_iff_integer_or_hasPositiveTwoThreeUnitPower
    {x gamma : ℝ}
    (hTwo : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (hThree : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (hgamma : 0 < gamma) (hgammaAlg : IsAlgebraic ℚ gamma) :
    IsAlgebraic ℚ (gamma ^ x) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) ∨ HasPositiveTwoThreeUnitPower gamma := by
  by_cases hxint : x ∈ Set.range ((↑) : ℤ → ℝ)
  · constructor
    · intro _
      exact Or.inl hxint
    · intro _
      exact real_rpow_isAlgebraic_of_integer_exponent hgammaAlg hxint
  · have hx : TwoBaseNonintegerSolution x :=
      ⟨⟨hTwo, hThree⟩, hxint⟩
    rw [hx.real_rpow_isAlgebraic_iff_hasPositiveTwoThreeUnitPower
      hgamma hgammaAlg, or_iff_right hxint]

/-- If a positive algebraic base has no positive rational `2,3`-unit power, then
its output at every hypothetical nonintegral two-base solution is transcendental. -/
theorem TwoBaseNonintegerSolution.transcendental_real_rpow_of_no_positiveTwoThreeUnitPower
    {x gamma : ℝ} (hx : TwoBaseNonintegerSolution x)
    (hgamma : 0 < gamma) (hgammaAlg : IsAlgebraic ℚ gamma)
    (hno : ¬ HasPositiveTwoThreeUnitPower gamma) :
    Transcendental ℚ (gamma ^ x) := by
  intro hgammaPowAlg
  exact hno ((hx.real_rpow_isAlgebraic_iff_hasPositiveTwoThreeUnitPower
    hgamma hgammaAlg).mp hgammaPowAlg)

end

end LeanProofs.TwoBaseIntegerExponent
