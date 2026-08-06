import PolynomialFormulas.GaussianPolynomialApproximationCore
import PolynomialFormulas.GaussianPolynomialSolver

/-!
# Normalizing degree-at-most-four Gaussian-rational polynomials

The executable approximator searches certificates for monic polynomials.  This
module converts the public five-coefficient input to the bounded coefficient
representation and divides by its first nonzero leading coefficient.  The
normalization is exact Gaussian-rational arithmetic and preserves the complete
complex root multiset.
-/

namespace LeanProofs.PolynomialFormulas

namespace GaussianPolynomialApproximationNormalization

open GaussianPolynomialApproximationCore
open GaussianPolynomialApproximationCore.QPoly
open GaussianPolynomialSolver

/-- Store `a₀, ..., a₄` in increasing coefficient order. -/
def toQPoly (c : Coefficients) : QPoly4 :=
  ![c.a0, c.a1, c.a2, c.a3, c.a4]

/-- The public input is not the identically-zero polynomial. -/
def Nonzero (c : Coefficients) : Prop := toQPoly c ≠ zero 4

/-- First nonzero leading coefficient of a nonzero input. -/
def leading (c : Coefficients) : GaussianRat := leadingCoeff (toQPoly c)

/-- Exact monic normalization. -/
def monic (c : Coefficients) : QPoly4 :=
  scale (leading c)⁻¹ (toQPoly c)

theorem leading_ne_zero {c : Coefficients} (hc : Nonzero c) : leading c ≠ 0 := by
  intro h
  have hpoly : (toPolynomial (toQPoly c)).leadingCoeff = 0 := by
    rw [← leadingCoeff_eq_toPolynomial]
    exact h
  have hz : toPolynomial (toQPoly c) = 0 := Polynomial.leadingCoeff_eq_zero.mp hpoly
  apply hc
  exact toPolynomial_injective (by simpa using hz)

theorem toPolynomial_monic (c : Coefficients) :
    toPolynomial (monic c) = Polynomial.C (leading c)⁻¹ * toPolynomial (toQPoly c) := by
  simp only [monic, toPolynomial_scale]

theorem monic_is_monic {c : Coefficients} (hc : Nonzero c) :
    (toPolynomial (monic c)).Monic := by
  rw [toPolynomial_monic]
  rw [Polynomial.Monic, Polynomial.leadingCoeff_mul]
  rw [Polynomial.leadingCoeff_C]
  rw [← leadingCoeff_eq_toPolynomial]
  exact inv_mul_cancel₀ (leading_ne_zero hc)

theorem degree_monic {c : Coefficients} (hc : Nonzero c) :
    degree (monic c) = degree (toQPoly c) := by
  rw [degree_eq_natDegree, degree_eq_natDegree, toPolynomial_monic]
  rw [Polynomial.natDegree_mul]
  · simp
  · simp [leading_ne_zero hc]
  · intro hz
    apply hc
    exact toPolynomial_injective (by simpa using hz)

/-- The bounded coefficient representation has exactly the public evaluator. -/
theorem evalComplex_toQPoly (c : Coefficients) (x : ℂ) :
    evalComplex (toQPoly c) x = c.eval x := by
  rw [evalComplex_eq_sum]
  simp [toQPoly, Coefficients.eval, quartic, Fin.sum_univ_succ]
  ring

theorem toComplexPolynomial_monic (c : Coefficients) :
    toComplexPolynomial (monic c) =
      Polynomial.C ((GaussianRat.toComplex (leading c))⁻¹) *
        toComplexPolynomial (toQPoly c) := by
  rw [toComplexPolynomial_eq_map, toPolynomial_monic,
    Polynomial.map_mul, Polynomial.map_C]
  rw [← toComplexPolynomial_eq_map]
  rw [map_inv₀]
  rfl

/-- Dividing by a nonzero leading coefficient preserves roots with
multiplicity, not only their underlying set. -/
theorem roots_monic_eq {c : Coefficients} (hc : Nonzero c) :
    (toComplexPolynomial (monic c)).roots =
      (toComplexPolynomial (toQPoly c)).roots := by
  rw [toComplexPolynomial_monic]
  apply Polynomial.roots_C_mul
  simpa using GaussianRat.toComplex_ne_zero_of_ne_zero (leading_ne_zero hc)

end GaussianPolynomialApproximationNormalization

end LeanProofs.PolynomialFormulas
