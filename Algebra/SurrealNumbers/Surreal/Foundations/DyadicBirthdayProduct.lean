import Surreal.Foundations.DyadicBirthdayArithmetic

/-!
# The dyadic height bound for products

This proves the finite dyadic arithmetic in `lem:realproduct` of
`docs/surreal/gonshor-laurent-birthdays/article.tex`. The ceiling of the
absolute value is submultiplicative, and the logarithm of the reduced
denominator is subadditive. Their sum therefore satisfies the required
product bound, with zero factors handled separately.

The interpretation of `height` as the birthday of the actual sign-sequence
embedding, and the nondyadic real cases, are proved in separate modules.
-/

namespace Surreal.Foundations.DyadicBirthdayArithmetic

/-- Reducing a dyadic product cannot increase the sum of denominator exponents. -/
theorem log_den_mul_le (p q : Dyadic) :
    Nat.log 2 (p * q).den ≤ Nat.log 2 p.den + Nat.log 2 q.den := by
  have hden : (p * q).den ≤ p.den * q.den := by
    change (p * q).toRat.den ≤ p.toRat.den * q.toRat.den
    rw [Dyadic.toRat_mul]
    exact Nat.le_of_dvd (mul_pos p.den_pos q.den_pos) (Rat.mul_den_dvd _ _)
  obtain ⟨h, hh⟩ : ∃ h, 2 ^ h = p.den := by
    rw [← Submonoid.mem_powers_iff]
    exact p.den_mem_powers
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ k = q.den := by
    rw [← Submonoid.mem_powers_iff]
    exact q.den_mem_powers
  calc
    Nat.log 2 (p * q).den ≤ Nat.log 2 (p.den * q.den) := Nat.log_mono_right hden
    _ = Nat.log 2 p.den + Nat.log 2 q.den := by
      rw [← hh, ← hk, ← pow_add, Nat.log_pow (by decide),
        Nat.log_pow (by decide), Nat.log_pow (by decide)]

/-- The natural ceiling of the absolute value is submultiplicative. -/
theorem ceil_abs_mul_le (p q : Dyadic) :
    Nat.ceil |(p * q).toRat| ≤ Nat.ceil |p.toRat| * Nat.ceil |q.toRat| := by
  apply Nat.ceil_le.mpr
  rw [Dyadic.toRat_mul, abs_mul, Nat.cast_mul]
  exact mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (abs_nonneg _) (by positivity)

@[simp] theorem height_zero : height 0 = 0 := by
  simp [height]

/-- The finite dyadic case of the real scalar product birthday bound. -/
theorem height_mul_le (p q : Dyadic) : height (p * q) ≤ height p * height q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  have hpceil : 1 ≤ Nat.ceil |p.toRat| :=
    Nat.one_le_ceil_iff.mpr (abs_pos.mpr (Dyadic.toRat_eq_zero_iff.not.mpr hp))
  have hqceil : 1 ≤ Nat.ceil |q.toRat| :=
    Nat.one_le_ceil_iff.mpr (abs_pos.mpr (Dyadic.toRat_eq_zero_iff.not.mpr hq))
  have hceil := ceil_abs_mul_le p q
  have hden := log_den_mul_le p q
  unfold height
  nlinarith

end Surreal.Foundations.DyadicBirthdayArithmetic
