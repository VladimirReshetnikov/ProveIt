import FabiusFunction.FabiusLegendreRationalGram

/-!
# Exact low-order rational Legendre Gram data

The executable rational Legendre Gram matrix makes the first five
determinants available by finite computation.  Their order-five quotient
then gives the next monic orthogonal-polynomial norm and Jacobi
subdiagonal.  Casting the rational norm transports the result to every
genuine Fabius representative and hence to the corresponding squared
integral.

The index on `rvachevJacobiSubdiagonalRat_three` is zero-based: its value is
the coefficient customarily denoted `beta_4`.  All numerical certificates in
this file are exact rational computations.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

/-! ## Executable rational values -/

/-- The fourth nontrivial even-moment value (the raw eighth moment) is
`132809 / 32531625`. -/
theorem moment_four : moment 4 = 132809 / 32531625 := by
  native_decide

/-- The order-one rational Legendre Gram determinant is one. -/
@[simp]
theorem rvachevLegendreGramDetRat_one :
    rvachevLegendreGramDetRat 1 = 1 := by
  native_decide

/-- The order-two rational Legendre Gram determinant is `1 / 9`. -/
theorem rvachevLegendreGramDetRat_two :
    rvachevLegendreGramDetRat 2 = 1 / 9 := by
  native_decide

/-- The order-three rational Legendre Gram determinant is `8 / 2025`. -/
theorem rvachevLegendreGramDetRat_three :
    rvachevLegendreGramDetRat 3 = 8 / 2025 := by
  native_decide

/-- The order-four rational Legendre Gram determinant is
`39616 / 602791875`. -/
theorem rvachevLegendreGramDetRat_four :
    rvachevLegendreGramDetRat 4 = 39616 / 602791875 := by
  native_decide

/-- The order-five rational Legendre Gram determinant is
`16544275456 / 27453718922765625`. -/
theorem rvachevLegendreGramDetRat_five :
    rvachevLegendreGramDetRat 5 =
      16544275456 / 27453718922765625 := by
  native_decide

private theorem legendrePolynomialCoeffRat_four_four :
    legendrePolynomialCoeffRat 4 4 = 35 / 8 := by
  native_decide

/-! ## Norm and subdiagonal values -/

/-- The exact rational squared norm of the degree-four monic orthogonal
polynomial is `26727424 / 55791736875`. -/
theorem rvachevOrthoNormRat_four :
    rvachevOrthoNormRat 4 = 26727424 / 55791736875 := by
  rw [rvachevOrthoNormRat_eq_rvachevLegendreGramDetRat_ratio]
  norm_num [rvachevLegendreGramDetRat_five,
    rvachevLegendreGramDetRat_four,
    legendrePolynomialCoeffRat_four_four]

/-- The zero-based fourth Jacobi subdiagonal is
`835232 / 4640643`. -/
theorem rvachevJacobiSubdiagonalRat_three :
    rvachevJacobiSubdiagonalRat 3 = 835232 / 4640643 := by
  rw [rvachevJacobiSubdiagonalRat_eq_rvachevLegendreGramDetRat_ratio]
  norm_num [rvachevLegendreGramDetRat_five,
    rvachevLegendreGramDetRat_four,
    rvachevLegendreGramDetRat_three]

/-! ## Real and integral consequences -/

/-- The degree-four Hankel ratio of every genuine Fabius representative is
`26727424 / 55791736875`. -/
theorem hankelRatio_four (F : BoundedFabius) (hF : IsFabius F) :
    hankelRatio F 4 = 26727424 / 55791736875 := by
  rw [← rvachevOrthoNormRat_cast F hF 4, rvachevOrthoNormRat_four]
  norm_num

/-- The squared `L²` norm of the degree-four monic orthogonal polynomial is
`26727424 / 55791736875`. -/
theorem integral_sq_upOrthoPolynomial_four
    (F : BoundedFabius) (hF : IsFabius F) :
    ∫ x, (upOrthoPolynomial F 4).eval x ^ 2 ∂(rvachevMeasure F) =
      26727424 / 55791736875 := by
  rw [integral_upOrthoPolynomial_sq F hF 4, hankelRatio_four F hF]

/-- The quotient of the fourth and third real Hankel ratios is
`835232 / 4640643`, the conventional Jacobi coefficient `beta_4`. -/
theorem hankelRatio_four_div_three
    (F : BoundedFabius) (hF : IsFabius F) :
    hankelRatio F 4 / hankelRatio F 3 = 835232 / 4640643 := by
  rw [← rvachevJacobiSubdiagonalRat_cast F hF 3,
    rvachevJacobiSubdiagonalRat_three]
  norm_num

end Fabius
