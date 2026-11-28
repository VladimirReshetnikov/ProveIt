import GRHArticle.SingularModuli.HeckePackedPolynomialArithmetic
import GRHArticle.SingularModuli.RationalComplexEnclosure
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Rational interval evaluation of the diagonal cofactor

Horner evaluation certifies exclusion of zero on a complex rectangle.
The input polynomial is given by its increasing-order integer coefficients.
-/

namespace GRHArticle.SingularModuli

namespace RationalComplexBox

/-- Horner evaluation with outward rounding at each multiplication. -/
def evaluateIntegerCoefficients (B : RationalComplexBox) : List ℤ → RationalComplexBox
  | [] => point 0 0
  | a :: as => (point (a : ℚ) 0).add (B.mul (evaluateIntegerCoefficients B as))

theorem contains_evaluateIntegerCoefficients {B : RationalComplexBox} {z : ℂ}
    (hz : B.Contains z) (l : List ℤ) :
    (B.evaluateIntegerCoefficients l).Contains
      (Polynomial.aeval z (coefficientListPolynomial l)) := by
  induction l with
  | nil =>
    simp only [evaluateIntegerCoefficients, coefficientListPolynomial, map_zero]
    convert contains_point 0 0 using 1
    apply Complex.ext <;> norm_num
  | cons a as ih =>
    have ha : (point (a : ℚ) 0).Contains (a : ℂ) := by
      convert contains_point (a : ℚ) 0 using 1
      apply Complex.ext <;> simp
    simpa only [evaluateIntegerCoefficients, coefficientListPolynomial, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_int_eq, Int.coe_castRingHom] using
      contains_add ha (contains_mul hz ih)

/-- A strict bound in either coordinate suffices to exclude zero. -/
def ExcludesZero (A : RationalComplexBox) : Prop :=
  0 < A.re.lo ∨ A.re.hi < 0 ∨ 0 < A.im.lo ∨ A.im.hi < 0

instance (A : RationalComplexBox) : Decidable A.ExcludesZero := by
  unfold ExcludesZero
  infer_instance

theorem ne_zero_of_contains_of_excludesZero {A : RationalComplexBox} {z : ℂ}
    (hz : A.Contains z) (h : A.ExcludesZero) : z ≠ 0 := by
  rintro rfl
  obtain ⟨⟨hre₀, hre₁⟩, ⟨him₀, him₁⟩⟩ := hz
  simp only [Complex.zero_re, Complex.zero_im] at hre₀ hre₁ him₀ him₁
  rcases h with h | h | h | h
  · exact not_lt_of_ge hre₀ (by exact_mod_cast h)
  · exact not_lt_of_ge hre₁ (by exact_mod_cast h)
  · exact not_lt_of_ge him₀ (by exact_mod_cast h)
  · exact not_lt_of_ge him₁ (by exact_mod_cast h)

/-- Coordinate separation guarantees that the boxes have disjoint contents. -/
def Separated (A B : RationalComplexBox) : Prop :=
  A.re.hi < B.re.lo ∨ B.re.hi < A.re.lo ∨ A.im.hi < B.im.lo ∨ B.im.hi < A.im.lo

instance (A B : RationalComplexBox) : Decidable (A.Separated B) := by
  unfold Separated
  infer_instance

theorem ne_of_contains_of_separated {A B : RationalComplexBox} {z w : ℂ}
    (hz : A.Contains z) (hw : B.Contains w) (h : A.Separated B) : z ≠ w := by
  rintro rfl
  rcases h with h | h | h | h
  · exact not_lt_of_ge (hw.1.1.trans hz.1.2) (by exact_mod_cast h)
  · exact not_lt_of_ge (hz.1.1.trans hw.1.2) (by exact_mod_cast h)
  · exact not_lt_of_ge (hw.2.1.trans hz.2.2) (by exact_mod_cast h)
  · exact not_lt_of_ge (hz.2.1.trans hw.2.2) (by exact_mod_cast h)

end RationalComplexBox

end GRHArticle.SingularModuli
