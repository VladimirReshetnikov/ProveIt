import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-!
# Integer and Gaussian constant obstructions for the quadratic ideal formula

The arithmetic specializations in `odg:def:thm:ideal`. The equation
 a² = 2b² has only the zero solution over Z and Z[i]. Complex factorization
and irrational real proportionality prove the Gaussian assertion without
assuming a nonsquare property of Q(i).
-/

namespace Surreal.QuadraticIdeal

/-- An irrational multiple of an integer can be an integer only when both are zero. -/
theorem integer_irrational_proportion_zero (r : ℝ) (hr : Irrational r) (a b : ℤ)
    (h : (a : ℝ) = r * b) : a = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hb' : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
    exact hr.ne_rational a b ((eq_div_iff hb').mpr h.symm)
  rw [hb, Int.cast_zero, mul_zero] at h
  exact_mod_cast h

/-- The irrational real proportionality obstruction applies to both Gaussian coordinates. -/
theorem gaussian_irrational_proportion_zero (r : ℝ) (hr : Irrational r) (a b : GaussianInt)
    (h : GaussianInt.toComplex a = (r : ℂ) * GaussianInt.toComplex b) : a = 0 := by
  have hre : (a.re : ℝ) = r * b.re := by
    have he := congrArg Complex.re h
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      ← GaussianInt.intCast_re] using he
  have him : (a.im : ℝ) = r * b.im := by
    have he := congrArg Complex.im h
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      ← GaussianInt.intCast_im] using he
  have ha := integer_irrational_proportion_zero r hr a.re b.re hre
  have hb := integer_irrational_proportion_zero r hr a.im b.im him
  ext <;> assumption

/-- Zero quadratic norm over the ordinary integers forces the first coordinate to vanish. -/
theorem integer_square_eq_two_zero (a b : ℤ) (h : a ^ 2 = 2 * b ^ 2) : a = 0 := by
  have hs : (a : ℝ) ^ 2 = (Real.sqrt 2 * b) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    exact_mod_cast h
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with he | he
  · exact integer_irrational_proportion_zero _ irrational_sqrt_two a b he
  · exact integer_irrational_proportion_zero _ irrational_sqrt_two.neg a b
      (by simpa only [neg_mul] using he)

/-- Zero quadratic norm over the ordinary Gaussian integers forces the first coordinate to vanish. -/
theorem gaussian_square_eq_two_zero (a b : GaussianInt) (h : a ^ 2 = 2 * b ^ 2) : a = 0 := by
  have hs : GaussianInt.toComplex a ^ 2 =
      ((Real.sqrt 2 : ℂ) * GaussianInt.toComplex b) ^ 2 := by
    have hr : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [mul_pow, hr]
    simpa only [map_pow, map_mul, map_ofNat] using congrArg GaussianInt.toComplex h
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with he | he
  · exact gaussian_irrational_proportion_zero _ irrational_sqrt_two a b he
  · exact gaussian_irrational_proportion_zero _ irrational_sqrt_two.neg a b
      (by simpa only [Complex.ofReal_neg, neg_mul] using he)

end Surreal.QuadraticIdeal
