import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicThirdBase
import ExponentialIdentities.TwoBaseIntegerExponent.CoreIndependence

/-!
# Consequences of algebraic output at a natural base

This module combines `AlgebraicThirdBase` with the rational-output theorem and
primitive-core structure. It gives a pointwise classification of algebraic
natural-base outputs, its exact noninteger specialization, primitive-core and
iterated-output transcendence consequences, and three equivalent algebraic-output
formulations of the Alaoglu--Erdős conjecture.
-/

open scoped Nat

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

private theorem nat_rpow_isAlgebraic_of_integer
    {a : ℕ} {x : ℝ} (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) :
    IsAlgebraic ℚ ((a : ℝ) ^ x) := by
  obtain ⟨k, rfl⟩ := hx
  rw [Real.rpow_intCast]
  have hcast : ((((a : ℚ) ^ k : ℚ) : ℝ)) = (a : ℝ) ^ k := by
    simpa only [Rat.cast_zpow, Rat.cast_natCast]
  rw [← hcast]
  exact isAlgebraic_rat ℚ ((a : ℚ) ^ k)

private theorem iterated_nat_rpow_isAlgebraic_of_integer
    (a : ℕ) {x : ℝ} (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) :
    IsAlgebraic ℚ (((a : ℝ) ^ x) ^ x) := by
  obtain ⟨k, rfl⟩ := hx
  simp only [Real.rpow_intCast]
  have hcast : (((((a : ℚ) ^ k) ^ k : ℚ) : ℝ)) = ((a : ℝ) ^ k) ^ k := by
    simpa only [Rat.cast_zpow, Rat.cast_natCast]
  rw [← hcast]
  exact isAlgebraic_rat ℚ (((a : ℚ) ^ k) ^ k)

private theorem nat_rpow_isAlgebraic_of_two_pow_mul_three_pow
    {a : ℕ} {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (ha : ∃ u v : ℕ, a = 2 ^ u * 3 ^ v) :
    IsAlgebraic ℚ ((a : ℝ) ^ x) := by
  obtain ⟨u, v, rfl⟩ := ha
  obtain ⟨z₂, hz₂⟩ := h₂
  obtain ⟨z₃, hz₃⟩ := h₃
  have hout : ∃ z : ℤ, (z : ℝ) = ((2 ^ u * 3 ^ v : ℕ) : ℝ) ^ x := by
    refine ⟨z₂ ^ u * z₃ ^ v, ?_⟩
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x u,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x v]
    rw [← hz₂, ← hz₃]
  obtain ⟨z, hz⟩ := hout
  rw [← hz]
  exact isAlgebraic_int z

/-- Pointwise classification with no nonintegrality assumption: algebraicity of a
positive natural-base output comes either from an integral exponent or from the base
already lying in the `2,3`-smooth monoid. -/
theorem rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    {a : ℕ} (ha : 0 < a) :
    IsAlgebraic ℚ ((a : ℝ) ^ x) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) ∨
        ∃ u v : ℕ, a = 2 ^ u * 3 ^ v := by
  constructor
  · intro haAlg
    by_cases hx : x ∈ Set.range ((↑) : ℤ → ℝ)
    · exact Or.inl hx
    · right
      rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow ha]
      intro p hp hpa
      by_contra hp23
      have hp2 : p ≠ 2 := fun h ↦ hp23 (Or.inl h)
      have hp3 : p ≠ 3 := fun h ↦ hp23 (Or.inr h)
      have ha1 : 1 < a := hp.one_lt.trans_le (Nat.le_of_dvd ha hpa)
      exact hx (integer_of_two_three_a_rpow_isAlgebraic_of_monomial_injective
        ha1 (monomial_injective_of_prime_dvd_ne_two_three ha hp hpa hp2 hp3)
        h₂ h₃ haAlg)
  · rintro (hx | hsmooth)
    · exact nat_rpow_isAlgebraic_of_integer hx
    · exact nat_rpow_isAlgebraic_of_two_pow_mul_three_pow h₂ h₃ hsmooth

/-- On a noninteger two-base solution, an algebraic natural-base output is exactly a
rational natural-base output. -/
theorem TwoBaseNonintegerSolution.rpow_isAlgebraic_iff_rational
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {a : ℕ} (ha : 0 < a) :
    IsAlgebraic ℚ ((a : ℝ) ^ x) ↔
      ∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x := by
  calc
    IsAlgebraic ℚ ((a : ℝ) ^ x) ↔
        x ∈ Set.range ((↑) : ℤ → ℝ) ∨
          ∃ u v : ℕ, a = 2 ^ u * 3 ^ v :=
      rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow hx.1.1 hx.1.2 ha
    _ ↔ ∃ u v : ℕ, a = 2 ^ u * 3 ^ v := by simp only [hx.2, false_or]
    _ ↔ ∃ q : ℚ, (q : ℝ) = (a : ℝ) ^ x :=
      (hx.rpow_rational_iff_eq_two_pow_mul_three_pow ha).symm

/-- On a noninteger two-base solution, algebraicity of a positive natural-base output
is also equivalent to integrality of that output. -/
theorem TwoBaseNonintegerSolution.rpow_isAlgebraic_iff_integer
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {a : ℕ} (ha : 0 < a) :
    IsAlgebraic ℚ ((a : ℝ) ^ x) ↔
      ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x := by
  calc
    IsAlgebraic ℚ ((a : ℝ) ^ x) ↔
        x ∈ Set.range ((↑) : ℤ → ℝ) ∨
          ∃ u v : ℕ, a = 2 ^ u * 3 ^ v :=
      rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow hx.1.1 hx.1.2 ha
    _ ↔ ∃ u v : ℕ, a = 2 ^ u * 3 ^ v := by simp only [hx.2, false_or]
    _ ↔ ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x :=
      (rpow_integer_iff_eq_two_pow_mul_three_pow_of_not_integer
        hx.2 hx.1.1 hx.1.2 ha).symm

/-- An odd primitive core has algebraic `x`-th power precisely in the exceptional
case `w = 3`. -/
theorem TwoBaseNonintegerSolution.rpow_isAlgebraic_iff_eq_three_of_odd_primitive
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {w : ℕ} (hwodd : Odd w) (hw : 1 < w) (hprimitive : NatPowerPrimitive w) :
    IsAlgebraic ℚ ((w : ℝ) ^ x) ↔ w = 3 := by
  calc
    IsAlgebraic ℚ ((w : ℝ) ^ x) ↔
        ∃ q : ℚ, (q : ℝ) = (w : ℝ) ^ x :=
      hx.rpow_isAlgebraic_iff_rational (Nat.zero_lt_one.trans hw)
    _ ↔ w = 3 :=
      hx.rpow_rational_iff_eq_three_of_odd_primitive hwodd hw hprimitive

/-- A `3`-free primitive core has algebraic `x`-th power precisely in the exceptional
case `v = 2`. -/
theorem TwoBaseNonintegerSolution.rpow_isAlgebraic_iff_eq_two_of_three_free_primitive
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {v : ℕ} (hvthree : ¬ 3 ∣ v) (hv : 1 < v) (hprimitive : NatPowerPrimitive v) :
    IsAlgebraic ℚ ((v : ℝ) ^ x) ↔ v = 2 := by
  calc
    IsAlgebraic ℚ ((v : ℝ) ^ x) ↔
        ∃ q : ℚ, (q : ℝ) = (v : ℝ) ^ x :=
      hx.rpow_isAlgebraic_iff_rational (Nat.zero_lt_one.trans hv)
    _ ↔ v = 2 :=
      hx.rpow_rational_iff_eq_two_of_three_free_primitive hvthree hv hprimitive

theorem TwoBaseNonintegerSolution.transcendental_rpow_of_odd_primitive_ne_three
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {w : ℕ} (hwodd : Odd w) (hw : 1 < w) (hprimitive : NatPowerPrimitive w)
    (hw3 : w ≠ 3) :
    Transcendental ℚ ((w : ℝ) ^ x) := by
  intro hAlg
  exact hw3 ((hx.rpow_isAlgebraic_iff_eq_three_of_odd_primitive
    hwodd hw hprimitive).mp hAlg)

theorem TwoBaseNonintegerSolution.transcendental_rpow_of_three_free_primitive_ne_two
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {v : ℕ} (hvthree : ¬ 3 ∣ v) (hv : 1 < v) (hprimitive : NatPowerPrimitive v)
    (hv2 : v ≠ 2) :
    Transcendental ℚ ((v : ℝ) ^ x) := by
  intro hAlg
  exact hv2 ((hx.rpow_isAlgebraic_iff_eq_two_of_three_free_primitive
    hvthree hv hprimitive).mp hAlg)

/-- The first iterates of the two integral outputs cannot both be algebraic. -/
theorem TwoBaseNonintegerSolution.not_both_iterated_outputs_isAlgebraic
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    ¬ (IsAlgebraic ℚ (((2 : ℝ) ^ x) ^ x) ∧
      IsAlgebraic ℚ (((3 : ℝ) ^ x) ^ x)) := by
  rintro ⟨hiterTwo, hiterThree⟩
  obtain ⟨zTwo, hzTwo⟩ := hx.1.1
  obtain ⟨zThree, hzThree⟩ := hx.1.2
  have hzTwoPos : 0 < zTwo := by
    exact_mod_cast (hzTwo.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
  have hzThreePos : 0 < zThree := by
    exact_mod_cast (hzThree.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) x)
  let M : ℕ := zTwo.natAbs
  let B : ℕ := zThree.natAbs
  have hMpos : 0 < M := Int.natAbs_pos.mpr hzTwoPos.ne'
  have hBpos : 0 < B := Int.natAbs_pos.mpr hzThreePos.ne'
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
  have hMAlg : IsAlgebraic ℚ ((M : ℝ) ^ x) := by simpa only [hM] using hiterTwo
  have hBAlg : IsAlgebraic ℚ ((B : ℝ) ^ x) := by simpa only [hB] using hiterThree
  have hMRat := (hx.rpow_isAlgebraic_iff_rational hMpos).mp hMAlg
  have hBRat := (hx.rpow_isAlgebraic_iff_rational hBpos).mp hBAlg
  apply hx.not_both_iterated_outputs_rational
  exact ⟨by simpa only [hM] using hMRat, by simpa only [hB] using hBRat⟩

/-- At least one first iterated output is transcendental. -/
theorem TwoBaseNonintegerSolution.transcendental_iterated_output
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    Transcendental ℚ (((2 : ℝ) ^ x) ^ x) ∨
      Transcendental ℚ (((3 : ℝ) ^ x) ^ x) := by
  by_cases hTwo : IsAlgebraic ℚ (((2 : ℝ) ^ x) ^ x)
  · exact Or.inr (fun hThree ↦
      hx.not_both_iterated_outputs_isAlgebraic ⟨hTwo, hThree⟩)
  · exact Or.inl hTwo

/-- Equivalently, at least one of `2 ^ (x*x)` and `3 ^ (x*x)` is transcendental. -/
theorem TwoBaseNonintegerSolution.transcendental_squared_exponent_output
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    Transcendental ℚ ((2 : ℝ) ^ (x * x)) ∨
      Transcendental ℚ ((3 : ℝ) ^ (x * x)) := by
  simpa only [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) x x,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) x x] using
    hx.transcendental_iterated_output

/-- With an external prime in the natural base, algebraicity of the output is pointwise
equivalent to integrality of the exponent. -/
theorem rpow_isAlgebraic_iff_integer_of_prime_factor_ne_two_three
    {a p : ℕ} (ha : 0 < a) (hp : p.Prime) (hpa : p ∣ a)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x) :
    IsAlgebraic ℚ ((a : ℝ) ^ x) ↔ x ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro hAlg
    rcases (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
      h₂ h₃ ha).mp hAlg with hx | hsmooth
    · exact hx
    · have hall :=
        (Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow ha).mpr hsmooth
      rcases hall p hp hpa with hp2' | hp3'
      · exact (hp2 hp2').elim
      · exact (hp3 hp3').elim
  · intro hx
    exact nat_rpow_isAlgebraic_of_integer hx

/-- Under the two integrality hypotheses, both first iterates are algebraic exactly when
the exponent is integral. -/
theorem both_iterated_outputs_isAlgebraic_iff_integer
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x) :
    (IsAlgebraic ℚ (((2 : ℝ) ^ x) ^ x) ∧
      IsAlgebraic ℚ (((3 : ℝ) ^ x) ^ x)) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro hAlg
    by_contra hxint
    exact (show TwoBaseNonintegerSolution x from ⟨⟨h₂, h₃⟩, hxint⟩).not_both_iterated_outputs_isAlgebraic hAlg
  · intro hxint
    exact ⟨iterated_nat_rpow_isAlgebraic_of_integer 2 hxint,
      iterated_nat_rpow_isAlgebraic_of_integer 3 hxint⟩

private theorem eq_two_pow_mul_three_pow_of_dvd
    {m A : ℕ} (hm : 0 < m) (hApos : 0 < A) (hdiv : m ∣ A)
    (hA : ∃ u v : ℕ, A = 2 ^ u * 3 ^ v) :
    ∃ u v : ℕ, m = 2 ^ u * 3 ^ v := by
  rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow hm]
  intro p hp hpm
  exact (Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow
    hApos).mpr hA p hp (dvd_trans hpm hdiv)

/-- A noninteger two-base solution forces the single intrinsic iterate
`6 ^ (x*x)` to be transcendental. -/
theorem TwoBaseNonintegerSolution.transcendental_six_squared_exponent_output
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) :
    Transcendental ℚ ((6 : ℝ) ^ (x * x)) := by
  intro hSixAlg
  obtain ⟨zTwo, hzTwo⟩ := hx.1.1
  obtain ⟨zThree, hzThree⟩ := hx.1.2
  have hzTwoPos : 0 < zTwo := by
    exact_mod_cast (hzTwo.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
  have hzThreePos : 0 < zThree := by
    exact_mod_cast (hzThree.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) x)
  let M : ℕ := zTwo.natAbs
  let B : ℕ := zThree.natAbs
  let A : ℕ := M * B
  have hMpos : 0 < M := Int.natAbs_pos.mpr hzTwoPos.ne'
  have hBpos : 0 < B := Int.natAbs_pos.mpr hzThreePos.ne'
  have hApos : 0 < A := mul_pos hMpos hBpos
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
  have hA : (A : ℝ) = (6 : ℝ) ^ x := by
    calc
      (A : ℝ) = (M : ℝ) * (B : ℝ) := by simp only [A, Nat.cast_mul]
      _ = (2 : ℝ) ^ x * (3 : ℝ) ^ x := by rw [hM, hB]
      _ = (6 : ℝ) ^ x := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
  have hAAlg : IsAlgebraic ℚ ((A : ℝ) ^ x) := by
    rw [hA]
    simpa only [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6) x x] using hSixAlg
  rcases (rpow_isAlgebraic_iff_integer_or_eq_two_pow_mul_three_pow
    hx.1.1 hx.1.2 hApos).mp hAAlg with hxint | hAsmooth
  · exact hx.2 hxint
  · have hMsmooth : ∃ u v : ℕ, M = 2 ^ u * 3 ^ v :=
      eq_two_pow_mul_three_pow_of_dvd hMpos hApos (by exact ⟨B, rfl⟩) hAsmooth
    have hBsmooth : ∃ u v : ℕ, B = 2 ^ u * 3 ^ v :=
      eq_two_pow_mul_three_pow_of_dvd hBpos hApos
        (by exact ⟨M, by simp [A, mul_comm]⟩) hAsmooth
    apply hx.not_both_iterated_outputs_isAlgebraic
    constructor
    · simpa only [hM] using
        nat_rpow_isAlgebraic_of_two_pow_mul_three_pow hx.1.1 hx.1.2 hMsmooth
    · simpa only [hB] using
        nat_rpow_isAlgebraic_of_two_pow_mul_three_pow hx.1.1 hx.1.2 hBsmooth

/-- Under the two original integrality hypotheses, algebraicity of the single
base-`6` squared-exponent output is exactly integrality of the exponent. -/
theorem six_squared_exponent_isAlgebraic_iff_integer
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x) :
    IsAlgebraic ℚ ((6 : ℝ) ^ (x * x)) ↔
      x ∈ Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · intro hAlg
    by_contra hxint
    exact (show TwoBaseNonintegerSolution x from
      ⟨⟨h₂, h₃⟩, hxint⟩).transcendental_six_squared_exponent_output hAlg
  · intro hxint
    simpa only [Nat.cast_ofNat,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6) x x] using
      iterated_nat_rpow_isAlgebraic_of_integer 6 hxint

/-- Alaoglu--Erdős is equivalent to algebraicity of the base-`5` output for every
two-base integral-power solution. -/
theorem alaogluErdosConjecture_iff_five_rpow_isAlgebraic :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        IsAlgebraic ℚ ((5 : ℝ) ^ x) := by
  constructor
  · intro hAE x hx
    exact nat_rpow_isAlgebraic_of_integer (hAE hx.1 hx.2)
  · intro hFive x h₂ h₃
    exact (rpow_isAlgebraic_iff_integer_of_prime_factor_ne_two_three
      (a := 5) (p := 5) (by norm_num) (by norm_num) (by simp)
      (by norm_num) (by norm_num) h₂ h₃).mp (hFive ⟨h₂, h₃⟩)

/-- Equivalently, Alaoglu--Erdős says that both first iterates are algebraic for every
two-base integral-power solution. -/
theorem alaogluErdosConjecture_iff_both_iterated_outputs_isAlgebraic :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        IsAlgebraic ℚ (((2 : ℝ) ^ x) ^ x) ∧
          IsAlgebraic ℚ (((3 : ℝ) ^ x) ^ x) := by
  constructor
  · intro hAE x hx
    exact (both_iterated_outputs_isAlgebraic_iff_integer hx.1 hx.2).mpr
      (hAE hx.1 hx.2)
  · intro hIter x h₂ h₃
    exact (both_iterated_outputs_isAlgebraic_iff_integer h₂ h₃).mp
      (hIter ⟨h₂, h₃⟩)

/-- Alaoglu--Erdős is equivalently the assertion that `6 ^ (x*x)` is algebraic
for every two-base integral-power solution. -/
theorem alaogluErdosConjecture_iff_six_squared_exponent_isAlgebraic :
    AlaogluErdosConjecture ↔
      ∀ {x : ℝ}, TwoBaseIntegralSolution x →
        IsAlgebraic ℚ ((6 : ℝ) ^ (x * x)) := by
  constructor
  · intro hAE x hx
    exact (six_squared_exponent_isAlgebraic_iff_integer hx.1 hx.2).mpr
      (hAE hx.1 hx.2)
  · intro hSix x h₂ h₃
    exact (six_squared_exponent_isAlgebraic_iff_integer h₂ h₃).mp
      (hSix ⟨h₂, h₃⟩)


end

end LeanProofs.TwoBaseIntegerExponent
