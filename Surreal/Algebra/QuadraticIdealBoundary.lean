import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# The polynomial obstruction to the quadratic ideal formula

The Z[omega] boundary example following `odg:def:thm:ideal`.
The coefficient of X² in X² is odd, whereas every coefficient in 2P²
is even. Injective polynomial evaluation transports this obstruction
to the actual generated subring in a Hahn workspace.
-/

namespace Surreal.QuadraticIdeal

/-- No integer polynomial can witness X² = 2P². -/
theorem integer_polynomial_X_no_quadratic_witness (P : Polynomial ℤ) :
    (Polynomial.X : Polynomial ℤ) ^ 2 ≠ 2 * P ^ 2 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff 2) h
  simp only [Polynomial.coeff_X_pow_self, Polynomial.coeff_ofNat_mul] at hc
  omega

/-- The same obstruction in the range subring of any faithful integer-polynomial evaluation. -/
theorem polynomial_range_no_quadratic_witness {R : Type*} [CommRing R]
    (φ : Polynomial ℤ →+* R) (hi : Function.Injective φ) :
    ¬ ∃ y : φ.range, (φ.rangeRestrict Polynomial.X) ^ 2 = 2 * y ^ 2 := by
  rintro ⟨y, hy⟩
  obtain ⟨P, hP⟩ := y.property
  have he := congrArg Subtype.val hy
  change (φ Polynomial.X) ^ 2 = 2 * y.val ^ 2 at he
  apply integer_polynomial_X_no_quadratic_witness P
  apply hi
  simpa only [map_pow, map_mul, map_ofNat, hP] using he

end Surreal.QuadraticIdeal
