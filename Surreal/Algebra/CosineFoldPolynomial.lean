import Surreal.Algebra.PolynomialMultiplicity

/-!
# Polynomial multiplicity at a cosine fold

The Laurent polynomial `(U + U⁻¹)/2 - (1-τ)` is represented by the
quadratic `U² - 2(1-τ)U + 1`. This generic finite algebra is the
polynomial-coordinate part of `trigonometry:thm:fold`.
-/

namespace Surreal.CosineFoldPolynomial

open Polynomial
noncomputable section
variable {K : Type*} [Field K]

/-- Clear the nonzero Laurent denominator `2U` in the cosine fold. -/
def polynomial (τ : K) : K[X] := X ^ 2 - C (2 * (1 - τ)) * X + 1

@[simp] theorem eval_polynomial (τ u : K) :
    (polynomial τ).eval u = u ^ 2 - 2 * (1 - τ) * u + 1 := by
  simp [polynomial]

/-- The quadratic is nonzero at every parameter, including collision. -/
theorem polynomial_ne_zero (τ : K) : polynomial τ ≠ 0 := by
  intro h
  have hc := congrArg (fun p : K[X] => p.coeff 2) h
  norm_num [polynomial, coeff_C_mul, coeff_one] at hc

@[simp] theorem eval_derivative (τ u : K) :
    (polynomial τ).derivative.eval u = 2 * (u - (1 - τ)) := by
  simp [polynomial]
  ring

/-- A root with nonzero derivative has native polynomial multiplicity one. -/
theorem multiplicity_one (τ u : K) (hu : (polynomial τ).eval u = 0)
    (hd : (polynomial τ).derivative.eval u ≠ 0) :
    (polynomial τ).rootMultiplicity u = 1 := by
  have hp : 0 < (polynomial τ).rootMultiplicity u :=
    (Polynomial.rootMultiplicity_pos (polynomial_ne_zero τ)).mpr hu
  have hnot : ¬ 1 < (polynomial τ).rootMultiplicity u := by
    rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot (polynomial_ne_zero τ)]
    exact fun h => hd h.2
  omega

/-- The colliding polynomial is exactly the square of its linear root factor. -/
theorem polynomial_zero : polynomial (0 : K) = (X - C 1) ^ 2 := by
  simp only [polynomial, sub_zero, mul_one, map_ofNat, map_one]
  ring

/-- The unique collision point has native polynomial multiplicity two. -/
theorem multiplicity_at_collision : (polynomial (0 : K)).rootMultiplicity 1 = 2 := by
  rw [polynomial_zero, Polynomial.rootMultiplicity_X_sub_C_pow]
/-- The exact polynomial obtained by multiplying `cos θ-(1-τ)` by `U`. -/
def laurentPolynomial (τ : K) : K[X] := C (1 / 2) * polynomial τ

/-- Multiplication by two recovers the monic quadratic, when two is nonzero. -/
theorem laurentPolynomial_eq (τ : K) (h2 : (2 : K) ≠ 0) :
    laurentPolynomial τ = C (1 / 2) * X ^ 2 - C (1 - τ) * X + C (1 / 2) := by
  have hc : C (1 / 2 : K) * C (2 * (1 - τ)) = C (1 - τ) := by
    rw [← map_mul]
    congr 1
    field_simp
  rw [laurentPolynomial, polynomial, mul_add, mul_sub, ← mul_assoc, hc, mul_one]

/-- The manuscript's normalization has exactly the same root multiplicities. -/
theorem multiplicity_laurentPolynomial (τ u : K) (h2 : (2 : K) ≠ 0) :
    (laurentPolynomial τ).rootMultiplicity u = (polynomial τ).rootMultiplicity u := by
  have hn : C (1 / 2 : K) * polynomial τ ≠ 0 :=
    mul_ne_zero (by simpa only [ne_eq, Polynomial.C_eq_zero] using
      (div_ne_zero (one_ne_zero : (1 : K) ≠ 0) h2)) (polynomial_ne_zero τ)
  rw [laurentPolynomial, Polynomial.rootMultiplicity_mul hn, Polynomial.rootMultiplicity_C, zero_add]


end
end Surreal.CosineFoldPolynomial
