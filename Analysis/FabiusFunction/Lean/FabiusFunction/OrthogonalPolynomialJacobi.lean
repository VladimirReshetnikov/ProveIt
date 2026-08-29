import FabiusFunction.OrthogonalPolynomialRecurrence

/-!
# The next exact Jacobi data of the up-law

The orthogonal-polynomial layer continued past `P₂ = x² - 1/9`.
Everything here is finite rational arithmetic on the up-measure's own
moments, so every constant below is an exact rational.

The moment recursion of `Arithmetic.lean` supplies the next two even
moments, `c₂ = 19/675` and `c₃ = 583/59535`; the odd moments vanish by
symmetry.  From `m₀, …, m₄` the `3 × 3` Hankel determinant is a
three-line computation, and it gives the Jacobi ratio `a₂ = h₃/h₂`;
the three-term recurrence then turns `a₂` into `P₃`.  For the next
step the `4 × 4` determinant is avoided altogether: the norm-producing
moment `∫ P₃(x)·x³ dμ_up = a₃` reduces `a₃` to `m₆ - (19/75)·m₄`, and
the recurrence again converts `a₃` into `P₄`.  The fourth Hankel
determinant is then recovered from `h₄ = a₃·h₃`.

* `moment_two`, `moment_three` — the executable rational moments
  `c₂ = 19/675` and `c₃ = 583/59535`;
* `upMoment_three`, `upMoment_four`, `upMoment_six` — the measure
  moments `m₃ = 0`, `m₄ = 19/675`, `m₆ = 583/59535`;
* `hankelDet_three` — `h₃ = 32/18225`;
* `hankelRatio_two` — **`a₂ = h₃/h₂ = 32/2025`**;
* `upOrthoPolynomial_three` — **`P₃ = x³ - (19/75)·x`**;
* `hankelRatio_three` — **`a₃ = 19808/7441875`**, from the norm
  identity rather than a `4 × 4` determinant;
* `hankelDet_four` — `h₄ = 633856/135628171875`;
* `upOrthoPolynomial_four` —
  **`P₄ = x⁴ - (62/147)·x² + 619/33075`**.

The Jacobi recurrence coefficients themselves are the quotients
`a₂/a₁ = 32/225` and `a₃/a₂ = 619/3675`, which appear inside the two
polynomial proofs.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

section RationalMoments

private theorem choose_five_two : Nat.choose 5 2 = 10 := by decide

private theorem choose_seven_two : Nat.choose 7 2 = 21 := by decide

private theorem choose_seven_four : Nat.choose 7 4 = 35 := by decide

private theorem fin_two_val_zero : ((0 : Fin 2) : ℕ) = 0 := rfl

private theorem fin_two_val_one : ((1 : Fin 2) : ℕ) = 1 := rfl

private theorem fin_three_val_zero : ((0 : Fin 3) : ℕ) = 0 := rfl

private theorem fin_three_val_one : ((1 : Fin 3) : ℕ) = 1 := rfl

private theorem fin_three_val_two : ((2 : Fin 3) : ℕ) = 2 := rfl

/-- **`c₂ = 19/675`**: the second nontrivial value of the executable
rational even-moment sequence, from its defining recurrence
`5·(2⁴-1)·c₂ = C(5,0)·c₀ + C(5,2)·c₁`. -/
theorem moment_two : moment 2 = 19 / 675 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, moment_succ]
  norm_num [Fin.sum_univ_two, Fin.sum_univ_succ, fin_two_val_zero,
    fin_two_val_one, moment_zero, moment_one, choose_five_two,
    Nat.choose]

/-- **`c₃ = 583/59535`**: the third nontrivial even moment, from
`7·(2⁶-1)·c₃ = C(7,0)·c₀ + C(7,2)·c₁ + C(7,4)·c₂`. -/
theorem moment_three : moment 3 = 583 / 59535 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, moment_succ]
  norm_num [Fin.sum_univ_three, Fin.sum_univ_succ, fin_three_val_zero,
    fin_three_val_one, fin_three_val_two, moment_zero, moment_one,
    moment_two, choose_seven_two, choose_seven_four, Nat.choose]

end RationalMoments

section MeasureMoments

/-- The third measure moment vanishes: odd moments of a symmetric
law. -/
theorem upMoment_three (F : BoundedFabius) (hF : IsFabius F) :
    upMoment F 3 = 0 := by
  have h := upMoment_odd F hF 1
  rwa [show (2 * 1 + 1 : ℕ) = 3 from rfl] at h

/-- The fourth measure moment is `19/675`. -/
theorem upMoment_four (F : BoundedFabius) (hF : IsFabius F) :
    upMoment F 4 = 19 / 675 := by
  have h := upMoment_even F hF 2
  rw [show (2 * 2 : ℕ) = 4 from rfl] at h
  rw [h, moment_two]
  norm_num

/-- The fifth measure moment vanishes. -/
theorem upMoment_five (F : BoundedFabius) (hF : IsFabius F) :
    upMoment F 5 = 0 := by
  have h := upMoment_odd F hF 2
  rwa [show (2 * 2 + 1 : ℕ) = 5 from rfl] at h

/-- The sixth measure moment is `583/59535`. -/
theorem upMoment_six (F : BoundedFabius) (hF : IsFabius F) :
    upMoment F 6 = 583 / 59535 := by
  have h := upMoment_even F hF 3
  rw [show (2 * 3 : ℕ) = 6 from rfl] at h
  rw [h, moment_three]
  norm_num

end MeasureMoments

section JacobiRatioTwo

/-- **`h₃ = 32/18225`**: the third Hankel determinant.  The two odd
moments in the `3 × 3` block vanish, so only `m₀m₂m₄` and `m₂³`
survive. -/
theorem hankelDet_three (F : BoundedFabius) (hF : IsFabius F) :
    hankelDet F 3 = 32 / 18225 := by
  rw [hankelDet, Matrix.det_fin_three]
  show upMoment F 0 * upMoment F 2 * upMoment F 4 -
      upMoment F 0 * upMoment F 3 * upMoment F 3 -
      upMoment F 1 * upMoment F 1 * upMoment F 4 +
      upMoment F 1 * upMoment F 3 * upMoment F 2 +
      upMoment F 2 * upMoment F 1 * upMoment F 3 -
      upMoment F 2 * upMoment F 2 * upMoment F 2 = 32 / 18225
  rw [upMoment_zero F hF, upMoment_one F hF, upMoment_two F hF,
    upMoment_three F hF, upMoment_four F hF]
  norm_num

/-- **The third Jacobi ratio**: `a₂ = h₃/h₂ = 32/2025` — equivalently
the squared `L²`-norm of `P₂ = x² - 1/9`. -/
theorem hankelRatio_two (F : BoundedFabius) (hF : IsFabius F) :
    hankelRatio F 2 = 32 / 2025 := by
  have h : hankelRatio F 2 = hankelDet F 3 / hankelDet F 2 := rfl
  rw [h, hankelDet_three F hF, hankelDet_two F hF]
  norm_num

/-- Norm form of `a₂`: `∫ P₂(x)² dμ_up = 32/2025`. -/
theorem integral_sq_upOrthoPolynomial_two (F : BoundedFabius)
    (hF : IsFabius F) :
    ∫ x, (upOrthoPolynomial F 2).eval x ^ 2 ∂(rvachevMeasure F) =
      32 / 2025 := by
  rw [integral_upOrthoPolynomial_sq F hF 2, hankelRatio_two F hF]

/-- **The fourth monic orthogonal polynomial**: `P₃ = x³ - (19/75)·x`.
The recurrence coefficient is `a₂/a₁ = (32/2025)/(1/9) = 32/225`, and
`1/9 + 32/225 = 19/75`. -/
theorem upOrthoPolynomial_three (F : BoundedFabius)
    (hF : IsFabius F) :
    upOrthoPolynomial F 3 =
      Polynomial.X ^ 3 -
        Polynomial.C (19 / 75 : ℝ) * Polynomial.X := by
  have h : Polynomial.X * upOrthoPolynomial F 2 =
      upOrthoPolynomial F 3 +
        Polynomial.C (hankelRatio F 2 / hankelRatio F 1) *
          upOrthoPolynomial F 1 :=
    upOrthoPolynomial_three_term F hF 1
  have hc : (32 / 2025 : ℝ) / (1 / 9) = 32 / 225 := by norm_num
  rw [upOrthoPolynomial_two F hF, upOrthoPolynomial_one F hF,
    hankelRatio_two F hF, hankelRatio_one F hF, hc] at h
  have h3 : upOrthoPolynomial F 3 =
      Polynomial.X *
          (Polynomial.X ^ 2 - Polynomial.C (1 / 9 : ℝ)) -
        Polynomial.C (32 / 225 : ℝ) * Polynomial.X := by
    rw [eq_sub_iff_add_eq]
    exact h.symm
  have hsum : (19 / 75 : ℝ) = 1 / 9 + 32 / 225 := by norm_num
  rw [h3, hsum, Polynomial.C_add]
  ring

/-- Pointwise form of `P₃`. -/
theorem upOrthoPolynomial_three_eval (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) :
    (upOrthoPolynomial F 3).eval x = x ^ 3 - 19 / 75 * x := by
  have h := congrArg (Polynomial.eval x)
    (upOrthoPolynomial_three F hF)
  simpa using h

end JacobiRatioTwo

section JacobiRatioThree

/-- **The fourth Jacobi ratio**: `a₃ = 19808/7441875`.  Instead of the
`4 × 4` Hankel determinant this reads the norm-producing moment
`∫ P₃(x)·x³ dμ_up = a₃`, which expands to `m₆ - (19/75)·m₄`. -/
theorem hankelRatio_three (F : BoundedFabius) (hF : IsFabius F) :
    hankelRatio F 3 = 19808 / 7441875 := by
  have hfun : (fun x : ℝ =>
      (upOrthoPolynomial F 3).eval x * x ^ 3) =
      fun x : ℝ => x ^ 6 - (19 / 75 : ℝ) * x ^ 4 := by
    funext x
    rw [upOrthoPolynomial_three F hF]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have h := integral_upOrthoPolynomial_mul_pow_self F hF 3
  rw [hfun, MeasureTheory.integral_sub
      (integrable_pow_rvachevMeasure F hF 6)
      ((integrable_pow_rvachevMeasure F hF 4).const_mul
        (19 / 75 : ℝ)),
    MeasureTheory.integral_const_mul] at h
  have hmom : upMoment F 6 - (19 / 75 : ℝ) * upMoment F 4 =
      hankelRatio F 3 := h
  rw [← hmom, upMoment_six F hF, upMoment_four F hF]
  norm_num

/-- Norm form of `a₃`: `∫ P₃(x)² dμ_up = 19808/7441875`. -/
theorem integral_sq_upOrthoPolynomial_three (F : BoundedFabius)
    (hF : IsFabius F) :
    ∫ x, (upOrthoPolynomial F 3).eval x ^ 2 ∂(rvachevMeasure F) =
      19808 / 7441875 := by
  rw [integral_upOrthoPolynomial_sq F hF 3, hankelRatio_three F hF]

/-- **`h₄ = 633856/135628171875`**: the fourth Hankel determinant,
recovered from `h₄ = a₃·h₃` rather than a `4 × 4` expansion. -/
theorem hankelDet_four (F : BoundedFabius) (hF : IsFabius F) :
    hankelDet F 4 = 633856 / 135628171875 := by
  have h : hankelDet F 4 / hankelDet F 3 = 19808 / 7441875 :=
    hankelRatio_three F hF
  rw [hankelDet_three F hF,
    div_eq_iff (by norm_num : (32 / 18225 : ℝ) ≠ 0)] at h
  rw [h]
  norm_num

/-- **The fifth monic orthogonal polynomial**:
`P₄ = x⁴ - (62/147)·x² + 619/33075`.  The recurrence coefficient is
`a₃/a₂ = (19808/7441875)/(32/2025) = 619/3675`, and
`19/75 + 619/3675 = 62/147`, `(619/3675)·(1/9) = 619/33075`. -/
theorem upOrthoPolynomial_four (F : BoundedFabius)
    (hF : IsFabius F) :
    upOrthoPolynomial F 4 =
      Polynomial.X ^ 4 -
        Polynomial.C (62 / 147 : ℝ) * Polynomial.X ^ 2 +
        Polynomial.C (619 / 33075 : ℝ) := by
  have h : Polynomial.X * upOrthoPolynomial F 3 =
      upOrthoPolynomial F 4 +
        Polynomial.C (hankelRatio F 3 / hankelRatio F 2) *
          upOrthoPolynomial F 2 :=
    upOrthoPolynomial_three_term F hF 2
  have hc : (19808 / 7441875 : ℝ) / (32 / 2025) = 619 / 3675 := by
    norm_num
  rw [upOrthoPolynomial_three F hF, upOrthoPolynomial_two F hF,
    hankelRatio_three F hF, hankelRatio_two F hF, hc] at h
  have h4 : upOrthoPolynomial F 4 =
      Polynomial.X *
          (Polynomial.X ^ 3 -
            Polynomial.C (19 / 75 : ℝ) * Polynomial.X) -
        Polynomial.C (619 / 3675 : ℝ) *
          (Polynomial.X ^ 2 - Polynomial.C (1 / 9 : ℝ)) := by
    rw [eq_sub_iff_add_eq]
    exact h.symm
  have hC1 : Polynomial.C (62 / 147 : ℝ) =
      Polynomial.C (19 / 75 : ℝ) +
        Polynomial.C (619 / 3675 : ℝ) := by
    rw [← Polynomial.C_add]
    norm_num
  have hC2 : Polynomial.C (619 / 33075 : ℝ) =
      Polynomial.C (619 / 3675 : ℝ) *
        Polynomial.C (1 / 9 : ℝ) := by
    rw [← Polynomial.C_mul]
    norm_num
  rw [h4, hC1, hC2]
  ring

/-- Pointwise form of `P₄`. -/
theorem upOrthoPolynomial_four_eval (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) :
    (upOrthoPolynomial F 4).eval x =
      x ^ 4 - 62 / 147 * x ^ 2 + 619 / 33075 := by
  have h := congrArg (Polynomial.eval x)
    (upOrthoPolynomial_four F hF)
  simpa using h

end JacobiRatioThree

end Fabius
