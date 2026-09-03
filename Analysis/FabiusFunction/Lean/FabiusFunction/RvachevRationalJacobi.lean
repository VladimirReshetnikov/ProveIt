import FabiusFunction.RvachevMomentAppell
import FabiusFunction.OrthogonalPolynomialGramBridge
import FabiusFunction.GramStieltjesNaturality
import FabiusFunction.MomentHankelValues

/-!
# The rational Jacobi system of the Rvachev up law

The full moment sequence of Rvachev's probability density is the cast of the
executable rational sequence `rvachevRawMomentRat`.  Naturality of the finite
Gram--Stieltjes construction therefore supplies exact rational Hankel
determinants, monic orthogonal polynomials, norms, and Jacobi subdiagonal
coefficients whose real casts are the corresponding objects of the up law.

The subdiagonal convention in this file is zero-based:
`rvachevJacobiSubdiagonalRat n` couples degrees `n + 1` and `n`.  Thus it is
the coefficient customarily denoted `β_(n+1)` in the recurrence
`π_(n+2) = x * π_(n+1) - β_(n+1) * π_n`.

The definitions remain the finite, adjugate-based Gram--Stieltjes objects and
are consequently noncomputable Lean definitions despite taking values in
`ℚ`.  The claims here concern exact algebraic rationality, not a native-code
evaluator.
-/

set_option autoImplicit false

open Polynomial

namespace Fabius

noncomputable section

/-- The order-`n` Hankel determinant of the rational Rvachev moments. -/
def rvachevHankelDetRat (n : ℕ) : ℚ :=
  momentHankelDet rvachevRawMomentRat n

/-- The degree-`n` monic Gram--Stieltjes polynomial over the rational
Rvachev moments. -/
def rvachevOrthoPolynomialRat (n : ℕ) : ℚ[X] :=
  gramStieltjesPolynomial rvachevRawMomentRat n

/-- The rational squared-norm quotient of the degree-`n` monic orthogonal
polynomial. -/
def rvachevOrthoNormRat (n : ℕ) : ℚ :=
  gramStieltjesNorm rvachevRawMomentRat n

/-- The zero-based rational Jacobi subdiagonal.  This is the coefficient
`β_(n+1)` coupling the monic polynomials of degrees `n + 1` and `n`. -/
def rvachevJacobiSubdiagonalRat (n : ℕ) : ℚ :=
  gramStieltjesJacobiSubdiagonal rvachevRawMomentRat n

/-- Every real up-law moment is the cast of the corresponding rational raw
Rvachev moment. -/
theorem upMoment_eq_rvachevRawMomentRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) :
    upMoment F r = (rvachevRawMomentRat r : ℝ) := by
  rw [upMoment_eq_integral_mul F hF,
    integral_pow_mul_rvachev_eq_rvachevRawMomentRat_cast F hF]

/-- Casting a rational Rvachev Hankel determinant to `ℝ` gives the Hankel
determinant of any analytic Fabius representative. -/
theorem rvachevHankelDetRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (rvachevHankelDetRat n : ℝ) = hankelDet F n := by
  unfold rvachevHankelDetRat
  change Rat.castHom ℝ (momentHankelDet rvachevRawMomentRat n) =
    hankelDet F n
  calc
    Rat.castHom ℝ (momentHankelDet rvachevRawMomentRat n) =
        momentHankelDet
          (fun k ↦ Rat.castHom ℝ (rvachevRawMomentRat k)) n :=
      map_momentHankelDet (Rat.castHom ℝ) rvachevRawMomentRat n
    _ = momentHankelDet (upMoment F) n := by
      apply congrArg (fun moment : ℕ → ℝ ↦ momentHankelDet moment n)
      funext k
      exact (upMoment_eq_rvachevRawMomentRat_cast F hF k).symm
    _ = hankelDet F n := (hankelDet_eq_momentHankelDet F n).symm

/-- Every rational Rvachev Hankel determinant is strictly positive. -/
theorem rvachevHankelDetRat_pos (n : ℕ) :
    0 < rvachevHankelDetRat n := by
  have hreal : (0 : ℝ) < (rvachevHankelDetRat n : ℝ) := by
    rw [rvachevHankelDetRat_cast fabius fabius_spec n]
    exact hankelDet_pos fabius fabius_spec n
  exact (Rat.cast_pos (K := ℝ)).mp hreal

/-- Mapping the rational Gram--Stieltjes polynomial to `ℝ` gives the monic
orthogonal polynomial of any analytic Fabius representative. -/
theorem rvachevOrthoPolynomialRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (rvachevOrthoPolynomialRat n).map (Rat.castHom ℝ) =
      upOrthoPolynomial F n := by
  unfold rvachevOrthoPolynomialRat
  calc
    (gramStieltjesPolynomial rvachevRawMomentRat n).map
        (Rat.castHom ℝ) =
      gramStieltjesPolynomial
        (fun k ↦ Rat.castHom ℝ (rvachevRawMomentRat k)) n :=
      map_gramStieltjesPolynomial
        (Rat.castHom ℝ) rvachevRawMomentRat n
    _ = gramStieltjesPolynomial (upMoment F) n := by
      apply congrArg
        (fun moment : ℕ → ℝ ↦ gramStieltjesPolynomial moment n)
      funext k
      exact (upMoment_eq_rvachevRawMomentRat_cast F hF k).symm
    _ = upOrthoPolynomial F n :=
      (upOrthoPolynomial_eq_gramStieltjesPolynomial F hF n).symm

/-- The rational Rvachev Gram--Stieltjes polynomial is monic of exact degree
`n`. -/
theorem rvachevOrthoPolynomialRat_isMonicOfDegree (n : ℕ) :
    Polynomial.IsMonicOfDegree (rvachevOrthoPolynomialRat n) n := by
  unfold rvachevOrthoPolynomialRat
  apply gramStieltjesPolynomial_isMonicOfDegree
  simpa only [rvachevHankelDetRat] using
    (ne_of_gt (rvachevHankelDetRat_pos n))

/-- The rational degree-`n` Rvachev polynomial is orthogonal, for the exact
rational moment pairing, to every polynomial of smaller degree. -/
theorem momentPairing_rvachevOrthoPolynomialRat_eq_zero
    (n : ℕ) (q : ℚ[X]) (hq : q.natDegree < n) :
    momentPairing rvachevRawMomentRat (rvachevOrthoPolynomialRat n) q = 0 := by
  simpa only [rvachevOrthoPolynomialRat] using
    momentPairing_gramStieltjesPolynomial_eq_zero
      rvachevRawMomentRat n q hq

/-- Casting the rational norm quotient to `ℝ` gives the corresponding
positive up-law Hankel ratio. -/
theorem rvachevOrthoNormRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (rvachevOrthoNormRat n : ℝ) = hankelRatio F n := by
  unfold rvachevOrthoNormRat
  change Rat.castHom ℝ (gramStieltjesNorm rvachevRawMomentRat n) =
    hankelRatio F n
  calc
    Rat.castHom ℝ (gramStieltjesNorm rvachevRawMomentRat n) =
        gramStieltjesNorm
          (fun k ↦ Rat.castHom ℝ (rvachevRawMomentRat k)) n :=
      map_gramStieltjesNorm (Rat.castHom ℝ) rvachevRawMomentRat n
    _ = gramStieltjesNorm (upMoment F) n := by
      apply congrArg (fun moment : ℕ → ℝ ↦ gramStieltjesNorm moment n)
      funext k
      exact (upMoment_eq_rvachevRawMomentRat_cast F hF k).symm
    _ = hankelRatio F n :=
      (hankelRatio_eq_gramStieltjesNorm F n).symm

/-- Every rational Rvachev Gram--Stieltjes norm quotient is positive. -/
theorem rvachevOrthoNormRat_pos (n : ℕ) :
    0 < rvachevOrthoNormRat n := by
  have hreal : (0 : ℝ) < (rvachevOrthoNormRat n : ℝ) := by
    rw [rvachevOrthoNormRat_cast fabius fabius_spec n]
    exact hankelRatio_pos fabius fabius_spec n
  exact (Rat.cast_pos (K := ℝ)).mp hreal

/-- Symmetry of the up law forces the rational Gram--Stieltjes Jacobi
diagonal to vanish. -/
theorem gramStieltjesJacobiDiagonal_rvachevRawMomentRat_eq_zero (n : ℕ) :
    gramStieltjesJacobiDiagonal rvachevRawMomentRat n = 0 := by
  apply Rat.cast_injective (α := ℝ)
  norm_num only [Rat.cast_zero]
  change Rat.castHom ℝ
      (gramStieltjesJacobiDiagonal rvachevRawMomentRat n) = 0
  calc
    Rat.castHom ℝ
        (gramStieltjesJacobiDiagonal rvachevRawMomentRat n) =
      gramStieltjesJacobiDiagonal
        (fun k ↦ Rat.castHom ℝ (rvachevRawMomentRat k)) n :=
      map_gramStieltjesJacobiDiagonal
        (Rat.castHom ℝ) rvachevRawMomentRat n
    _ = gramStieltjesJacobiDiagonal (upMoment fabius) n := by
      apply congrArg
        (fun moment : ℕ → ℝ ↦ gramStieltjesJacobiDiagonal moment n)
      funext k
      exact (upMoment_eq_rvachevRawMomentRat_cast
        fabius fabius_spec k).symm
    _ = 0 :=
      gramStieltjesJacobiDiagonal_upMoment_eq_zero
        fabius fabius_spec n

/-- Casting the zero-based rational subdiagonal gives the ratio of
consecutive real up-law norms. -/
theorem rvachevJacobiSubdiagonalRat_cast
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    (rvachevJacobiSubdiagonalRat n : ℝ) =
      hankelRatio F (n + 1) / hankelRatio F n := by
  unfold rvachevJacobiSubdiagonalRat
  change Rat.castHom ℝ
      (gramStieltjesJacobiSubdiagonal rvachevRawMomentRat n) =
    hankelRatio F (n + 1) / hankelRatio F n
  calc
    Rat.castHom ℝ
        (gramStieltjesJacobiSubdiagonal rvachevRawMomentRat n) =
      gramStieltjesJacobiSubdiagonal
        (fun k ↦ Rat.castHom ℝ (rvachevRawMomentRat k)) n :=
      map_gramStieltjesJacobiSubdiagonal
        (Rat.castHom ℝ) rvachevRawMomentRat n
    _ = gramStieltjesJacobiSubdiagonal (upMoment F) n := by
      apply congrArg
        (fun moment : ℕ → ℝ ↦ gramStieltjesJacobiSubdiagonal moment n)
      funext k
      exact (upMoment_eq_rvachevRawMomentRat_cast F hF k).symm
    _ = hankelRatio F (n + 1) / hankelRatio F n :=
      gramStieltjesJacobiSubdiagonal_upMoment_eq F n

/-- Every zero-based rational Rvachev Jacobi subdiagonal is positive. -/
theorem rvachevJacobiSubdiagonalRat_pos (n : ℕ) :
    0 < rvachevJacobiSubdiagonalRat n := by
  have hreal : (0 : ℝ) < (rvachevJacobiSubdiagonalRat n : ℝ) := by
    rw [rvachevJacobiSubdiagonalRat_cast fabius fabius_spec n]
    exact div_pos (hankelRatio_pos fabius fabius_spec (n + 1))
      (hankelRatio_pos fabius fabius_spec n)
  exact (Rat.cast_pos (K := ℝ)).mp hreal

/-- The zero-based rational Jacobi subdiagonal is the Hankel cross-ratio
`Δ_(n+2) * Δ_n / Δ_(n+1)^2`. -/
theorem rvachevJacobiSubdiagonalRat_eq_det_ratio (n : ℕ) :
    rvachevJacobiSubdiagonalRat n =
      rvachevHankelDetRat (n + 2) * rvachevHankelDetRat n /
        rvachevHankelDetRat (n + 1) ^ 2 := by
  simpa only [rvachevJacobiSubdiagonalRat, rvachevHankelDetRat] using
    gramStieltjesJacobiSubdiagonal_eq_det_ratio
      rvachevRawMomentRat n

/-- The exact rational monic recurrence.  Its zero-based coefficient
`rvachevJacobiSubdiagonalRat n` is the conventional `β_(n+1)`. -/
theorem rvachevOrthoPolynomialRat_three_term (n : ℕ) :
    rvachevOrthoPolynomialRat (n + 2) =
      Polynomial.X * rvachevOrthoPolynomialRat (n + 1) -
        Polynomial.C (rvachevJacobiSubdiagonalRat n) *
          rvachevOrthoPolynomialRat n := by
  change gramStieltjesPolynomial rvachevRawMomentRat (n + 2) =
    Polynomial.X *
        gramStieltjesPolynomial rvachevRawMomentRat (n + 1) -
      Polynomial.C
          (gramStieltjesJacobiSubdiagonal rvachevRawMomentRat n) *
        gramStieltjesPolynomial rvachevRawMomentRat n
  have hdet (k : ℕ) : momentHankelDet rvachevRawMomentRat k ≠ 0 := by
    simpa only [rvachevHankelDetRat] using
      (ne_of_gt (rvachevHankelDetRat_pos k))
  have hrec := gramStieltjesPolynomial_three_term
    rvachevRawMomentRat n (hdet n) (hdet (n + 1)) (hdet (n + 2))
  have hrec' :
      Polynomial.X *
          gramStieltjesPolynomial rvachevRawMomentRat (n + 1) =
        gramStieltjesPolynomial rvachevRawMomentRat (n + 2) +
          Polynomial.C
              (gramStieltjesJacobiSubdiagonal rvachevRawMomentRat n) *
            gramStieltjesPolynomial rvachevRawMomentRat n := by
    simpa only [
      gramStieltjesJacobiDiagonal_rvachevRawMomentRat_eq_zero,
      Polynomial.C_0, zero_mul, add_zero] using hrec
  rw [eq_sub_iff_add_eq]
  exact hrec'.symm

end

end Fabius
