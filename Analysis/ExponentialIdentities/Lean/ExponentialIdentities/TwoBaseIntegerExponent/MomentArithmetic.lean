import Mathlib.Tactic

namespace LeanProofs.TwoBaseIntegerExponent

/-!
# Finite moment arithmetic

This module verifies the bounded algebraic core of the additive Hausdorff-moment
continuation.  It contains the explicit rational two-atom reproduction theorem,
the four common-denominator identities for the rational moment defects, and the
local `2`/`3` noncancellation checks for their integer numerators.

The analytic Hausdorff representation, strict moment inequalities, rational
quadrature theorem in arbitrary finite dimension, and Muntz invisibility theorem
remain paper arguments.
-/

namespace MomentArithmetic

/-- Algebraic core of the rational two-atom quadrature theorem.  The node
`m₂ / m₁` and both weights are positive, the node is strictly below one, and
the resulting weighted power sums reproduce moments zero, one, and two. -/
theorem rational_twoAtom_reproduction
    (m₀ m₁ m₂ : ℚ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hm₂m₁ : m₂ < m₁) (hHankel : m₁ ^ 2 < m₀ * m₂) :
    let t := m₂ / m₁
    let w₀ := m₀ - m₁ ^ 2 / m₂
    let w₁ := m₁ ^ 2 / m₂
    0 < t ∧ t < 1 ∧ 0 < w₀ ∧ 0 < w₁ ∧
      w₀ + w₁ = m₀ ∧ w₁ * t = m₁ ∧ w₁ * t ^ 2 = m₂ := by
  dsimp
  have hm₁0 : m₁ ≠ 0 := ne_of_gt hm₁
  have hm₂0 : m₂ ≠ 0 := ne_of_gt hm₂
  refine ⟨div_pos hm₂ hm₁, (div_lt_one hm₁).2 hm₂m₁, ?_, ?_, ?_, ?_, ?_⟩
  · exact sub_pos.mpr ((div_lt_iff₀ hm₂).2 hHankel)
  · exact div_pos (sq_pos_of_pos hm₁) hm₂
  · field_simp [hm₂0]
    ring
  · field_simp [hm₁0, hm₂0]
  · field_simp [hm₁0, hm₂0]

/-- Common-denominator identity for the first Hankel defect. -/
theorem firstHankel_commonDenominator
    (T U A₀ A₁ A₂ : ℚ) (hT : T ≠ 0) (hU : U ≠ 0) :
    (A₀ / T) * (A₂ / (T ^ 2 * U)) - (A₁ / (T * U)) ^ 2 =
      (U * A₀ * A₂ - T * A₁ ^ 2) / (T ^ 3 * U ^ 2) := by
  field_simp [hT, hU]

/-- Common-denominator identity for the `(0,1,7)` log-convexity defect. -/
theorem defect017_commonDenominator
    (T U A₀ A₁ A₇ : ℚ) (hT : T ≠ 0) (hU : U ≠ 0) :
    (A₀ / T) ^ 6 * (A₇ / (T ^ 3 * U ^ 2)) - (A₁ / (T * U)) ^ 7 =
      (U ^ 5 * A₀ ^ 6 * A₇ - T ^ 2 * A₁ ^ 7) /
        (T ^ 9 * U ^ 7) := by
  field_simp [hT, hU]

/-- Common-denominator identity for the `(1,2,7)` log-convexity defect. -/
theorem defect127_commonDenominator
    (T U A₁ A₂ A₇ : ℚ) (hT : T ≠ 0) (hU : U ≠ 0) :
    (A₁ / (T * U)) ^ 5 * (A₇ / (T ^ 3 * U ^ 2)) -
        (A₂ / (T ^ 2 * U)) ^ 6 =
      (T ^ 4 * A₁ ^ 5 * A₇ - U * A₂ ^ 6) /
        (T ^ 12 * U ^ 7) := by
  field_simp [hT, hU]

/-- Common-denominator identity for the `(0,2,7)` log-convexity defect. -/
theorem defect027_commonDenominator
    (T U A₀ A₂ A₇ : ℚ) (hT : T ≠ 0) (hU : U ≠ 0) :
    (A₀ / T) ^ 5 * (A₇ / (T ^ 3 * U ^ 2)) ^ 2 -
        (A₂ / (T ^ 2 * U)) ^ 7 =
      (T ^ 3 * U ^ 3 * A₀ ^ 5 * A₇ ^ 2 - A₂ ^ 7) /
        (T ^ 14 * U ^ 7) := by
  field_simp [hT, hU]

private theorem twoPow_mul_even (k : ℕ) (hk : k ≠ 0) (z : ℤ) :
    Even ((2 : ℤ) ^ k * z) := by
  rw [even_iff_two_dvd]
  exact dvd_mul_of_dvd_left (dvd_pow_self (2 : ℤ) hk) z

private theorem threePow_mul_dvd (k : ℕ) (hk : k ≠ 0) (z : ℤ) :
    (3 : ℤ) ∣ (3 : ℤ) ^ k * z :=
  dvd_mul_of_dvd_left (dvd_pow_self (3 : ℤ) hk) z

private theorem three_not_dvd_pow {z : ℤ} (hz : ¬ (3 : ℤ) ∣ z)
    (k : ℕ) (hk : k ≠ 0) : ¬ (3 : ℤ) ∣ z ^ k := by
  intro h
  exact hz (((show Prime (3 : ℤ) by norm_num).dvd_pow_iff_dvd hk).mp h)

private theorem three_not_dvd_twoPow (k : ℕ) (hk : k ≠ 0) :
    ¬ (3 : ℤ) ∣ (2 : ℤ) ^ k := by
  apply three_not_dvd_pow (k := k) (by norm_num) hk

private theorem oddSubEven_not_three_dvd {L R : ℤ}
    (hLodd : Odd L) (hReven : Even R)
    (h3L : (3 : ℤ) ∣ L) (h3R : ¬ (3 : ℤ) ∣ R) :
    Odd (L - R) ∧ ¬ (3 : ℤ) ∣ L - R := by
  refine ⟨hLodd.sub_even hReven, ?_⟩
  intro h
  apply h3R
  have hsub := dvd_sub h3L h
  have heq : L - (L - R) = R := by ring
  rw [heq] at hsub
  exact hsub

private theorem evenSubOdd_not_three_dvd {L R : ℤ}
    (hLeven : Even L) (hRodd : Odd R)
    (h3L : ¬ (3 : ℤ) ∣ L) (h3R : (3 : ℤ) ∣ R) :
    Odd (L - R) ∧ ¬ (3 : ℤ) ∣ L - R := by
  refine ⟨hLeven.sub_odd hRodd, ?_⟩
  intro h
  apply h3L
  have hadd := dvd_add h h3R
  simpa only [sub_add_cancel] using hadd

private theorem evenSubOdd_not_three_dvd_of_left {L R : ℤ}
    (hLeven : Even L) (hRodd : Odd R)
    (h3L : (3 : ℤ) ∣ L) (h3R : ¬ (3 : ℤ) ∣ R) :
    Odd (L - R) ∧ ¬ (3 : ℤ) ∣ L - R := by
  refine ⟨hLeven.sub_odd hRodd, ?_⟩
  intro h
  apply h3R
  have hsub := dvd_sub h3L h
  have heq : L - (L - R) = R := by ring
  rw [heq] at hsub
  exact hsub

/-- The first Hankel numerator is odd and remains a unit at `3` whenever
`r,s > 0` and the displayed triadic unit hypothesis holds. -/
theorem firstHankel_numerator_localUnits
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (A₀ A₁ A₂ : ℤ)
    (hA₀ : Odd A₀) (hA₁3 : ¬ (3 : ℤ) ∣ A₁) (hA₂ : Odd A₂) :
    Odd ((3 : ℤ) ^ s * A₀ * A₂ - (2 : ℤ) ^ r * A₁ ^ 2) ∧
      ¬ (3 : ℤ) ∣ (3 : ℤ) ^ s * A₀ * A₂ - (2 : ℤ) ^ r * A₁ ^ 2 := by
  apply oddSubEven_not_three_dvd
  · exact ((show Odd (3 : ℤ) by norm_num).pow.mul hA₀).mul hA₂
  · exact twoPow_mul_even r (by omega) (A₁ ^ 2)
  · simpa [mul_assoc] using threePow_mul_dvd s (by omega) (A₀ * A₂)
  · exact (show Prime (3 : ℤ) by norm_num).not_dvd_mul
      (three_not_dvd_twoPow r (by omega))
      (three_not_dvd_pow hA₁3 2 (by norm_num))

/-- The `(0,1,7)` numerator is odd and a unit at `3`. -/
theorem defect017_numerator_localUnits
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (A₀ A₁ A₇ : ℤ)
    (hA₀ : Odd A₀) (hA₁3 : ¬ (3 : ℤ) ∣ A₁) (hA₇ : Odd A₇) :
    Odd ((3 : ℤ) ^ (5 * s) * A₀ ^ 6 * A₇ -
      (2 : ℤ) ^ (2 * r) * A₁ ^ 7) ∧
      ¬ (3 : ℤ) ∣ (3 : ℤ) ^ (5 * s) * A₀ ^ 6 * A₇ -
        (2 : ℤ) ^ (2 * r) * A₁ ^ 7 := by
  apply oddSubEven_not_three_dvd
  · exact (((show Odd (3 : ℤ) by norm_num).pow.mul hA₀.pow).mul hA₇)
  · exact twoPow_mul_even (2 * r) (by omega) (A₁ ^ 7)
  · simpa [mul_assoc] using
      threePow_mul_dvd (5 * s) (by omega) (A₀ ^ 6 * A₇)
  · exact (show Prime (3 : ℤ) by norm_num).not_dvd_mul
      (three_not_dvd_twoPow (2 * r) (by omega))
      (three_not_dvd_pow hA₁3 7 (by norm_num))

/-- The `(1,2,7)` numerator is odd and a unit at `3`. -/
theorem defect127_numerator_localUnits
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (A₁ A₂ A₇ : ℤ)
    (hA₁3 : ¬ (3 : ℤ) ∣ A₁) (hA₂ : Odd A₂)
    (hA₇3 : ¬ (3 : ℤ) ∣ A₇) :
    Odd ((2 : ℤ) ^ (4 * r) * A₁ ^ 5 * A₇ - (3 : ℤ) ^ s * A₂ ^ 6) ∧
      ¬ (3 : ℤ) ∣ (2 : ℤ) ^ (4 * r) * A₁ ^ 5 * A₇ -
        (3 : ℤ) ^ s * A₂ ^ 6 := by
  apply evenSubOdd_not_three_dvd
  · simpa [mul_assoc] using
      twoPow_mul_even (4 * r) (by omega) (A₁ ^ 5 * A₇)
  · exact (show Odd (3 : ℤ) by norm_num).pow.mul hA₂.pow
  · exact (show Prime (3 : ℤ) by norm_num).not_dvd_mul
      ((show Prime (3 : ℤ) by norm_num).not_dvd_mul
        (three_not_dvd_twoPow (4 * r) (by omega))
        (three_not_dvd_pow hA₁3 5 (by norm_num))) hA₇3
  · exact threePow_mul_dvd s (by omega) (A₂ ^ 6)

/-- The `(0,2,7)` numerator is odd and a unit at `3`. -/
theorem defect027_numerator_localUnits
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (A₀ A₂ A₇ : ℤ)
    (hA₂ : Odd A₂) (hA₂3 : ¬ (3 : ℤ) ∣ A₂) :
    Odd ((2 : ℤ) ^ (3 * r) * (3 : ℤ) ^ (3 * s) * A₀ ^ 5 * A₇ ^ 2 -
      A₂ ^ 7) ∧
      ¬ (3 : ℤ) ∣ (2 : ℤ) ^ (3 * r) * (3 : ℤ) ^ (3 * s) *
        A₀ ^ 5 * A₇ ^ 2 - A₂ ^ 7 := by
  apply evenSubOdd_not_three_dvd_of_left
  · have h := twoPow_mul_even (3 * r) (by omega)
      ((3 : ℤ) ^ (3 * s) * A₀ ^ 5 * A₇ ^ 2)
    simpa [mul_assoc] using h
  · exact hA₂.pow
  · have h3 : (3 : ℤ) ∣
        (3 : ℤ) ^ (3 * s) * (A₀ ^ 5 * A₇ ^ 2) :=
      threePow_mul_dvd (3 * s) (by omega) (A₀ ^ 5 * A₇ ^ 2)
    have hmul := dvd_mul_of_dvd_right h3 ((2 : ℤ) ^ (3 * r))
    simpa [mul_assoc] using hmul
  · exact three_not_dvd_pow hA₂3 7 (by norm_num)

end MomentArithmetic

end LeanProofs.TwoBaseIntegerExponent
