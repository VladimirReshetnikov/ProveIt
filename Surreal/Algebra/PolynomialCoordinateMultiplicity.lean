import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-!
# Polynomial root multiplicity in a formal local coordinate

The algebraic coordinate-change step of `trigonometry:thm:polyroots`.
A polynomial evaluated in a series centered at `a` has order equal to its
root multiplicity at `a` times the order of the coordinate increment.
A nonzero linear coefficient therefore preserves multiplicity, as does
multiplication by a series with nonzero constant coefficient.
-/

namespace Surreal.PolynomialCoordinateMultiplicity

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Taking the constant coefficient commutes with polynomial evaluation in a series. -/
theorem constantCoeff_eval (P : K[X]) (φ : PowerSeries K) :
    (P.eval₂ PowerSeries.C φ).constantCoeff = P.eval φ.constantCoeff := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [eval₂_add, map_add, eval_add, hP, hQ]
  | monomial n a => simp [eval₂_monomial, eval_monomial]

/-- A series with nonzero constant coefficient has order zero. -/
theorem order_zero_of_constantCoeff_ne_zero (φ : PowerSeries K)
    (hφ : φ.constantCoeff ≠ 0) : φ.order = 0 := by
  by_contra h
  exact hφ (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h)

/-- The ramified coordinate formula, before specializing the coordinate order to one. -/
theorem order_eval (P : K[X]) (hP : P ≠ 0) (a : K) (φ : PowerSeries K)
    (hφ : φ.constantCoeff = a) :
    (P.eval₂ PowerSeries.C φ).order = P.rootMultiplicity a • (φ - PowerSeries.C a).order := by
  let Q := P /ₘ (Polynomial.X - Polynomial.C a) ^ P.rootMultiplicity a
  have hQ : Q.eval a ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hP
  have hunit : (Q.eval₂ PowerSeries.C φ).order = 0 := by
    apply order_zero_of_constantCoeff_ne_zero
    rw [constantCoeff_eval, hφ]
    exact hQ
  have he := congrArg (Polynomial.eval₂RingHom PowerSeries.C φ)
    (P.pow_mul_divByMonic_rootMultiplicity_eq a)
  change ((Polynomial.X - Polynomial.C a) ^ P.rootMultiplicity a * Q).eval₂
    PowerSeries.C φ = P.eval₂ PowerSeries.C φ at he
  rw [eval₂_mul, eval₂_pow, eval₂_sub, eval₂_X, eval₂_C] at he
  rw [← he, PowerSeries.order_mul, PowerSeries.order_pow, hunit, add_zero]

/-- A coordinate centered at `a` with nonzero linear coefficient preserves root multiplicity. -/
theorem order_eval_of_linear_ne_zero (P : K[X]) (hP : P ≠ 0) (a : K)
    (φ : PowerSeries K) (hφ : φ.constantCoeff = a) (hlinear : φ.coeff 1 ≠ 0) :
    (P.eval₂ PowerSeries.C φ).order = (P.rootMultiplicity a : ℕ∞) := by
  have ho : (φ - PowerSeries.C a).order = 1 := by
    apply PowerSeries.order_eq_nat.mpr
    constructor
    · simpa [PowerSeries.coeff_C] using hlinear
    · intro n hn
      have hn0 : n = 0 := by omega
      subst n
      simp [PowerSeries.coeff_zero_eq_constantCoeff, hφ]
  rw [order_eval P hP a φ hφ, ho]
  simp

/-- Removing any formal unit factor preserves the same local multiplicity. -/
theorem order_unit_mul_eval (P : K[X]) (hP : P ≠ 0) (a : K)
    (φ U : PowerSeries K) (hφ : φ.constantCoeff = a) (hlinear : φ.coeff 1 ≠ 0)
    (hU : U.constantCoeff ≠ 0) :
    (U * P.eval₂ PowerSeries.C φ).order = (P.rootMultiplicity a : ℕ∞) := by
  rw [PowerSeries.order_mul, order_zero_of_constantCoeff_ne_zero U hU,
    order_eval_of_linear_ne_zero P hP a φ hφ hlinear, zero_add]

end
end Surreal.PolynomialCoordinateMultiplicity
