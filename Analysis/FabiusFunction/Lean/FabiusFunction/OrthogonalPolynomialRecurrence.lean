import FabiusFunction.OrthogonalPolynomialParity
import FabiusFunction.OrthogonalPolynomialValues

/-!
# The three-term recurrence of the up-measure's orthogonal polynomials

The J-fraction core of the integration volume's orthogonal-polynomial
layer: the monic orthogonal polynomials of the up-measure satisfy

`x·P_{n+1} = P_{n+2} + (a_{n+1}/a_n)·P_n`,   `x·P₀ = P₁`,

where `a_n = h_{n+1}/h_n` is the Hankel ratio — by the norm identity,
the squared `L²`-norm of `P_n` — so the recurrence coefficient is the
ratio of consecutive squared norms.  The Jacobi `b`-coefficients
vanish because the measure is symmetric.

The proof is pure Hilbert-space bookkeeping made polynomial: the
defect `r = x·P_{n+1} - P_{n+2} - (a_{n+1}/a_n)·P_n` has degree
`≤ n+1` (the two monic leading terms cancel) and is orthogonal to
`x^j` for every `j < n+2` — below `j = n` by plain orthogonality, at
`j = n` because the two Hankel-ratio contributions cancel exactly,
and at `j = n+1` by parity — so `r` has zero squared mass and
vanishes.

`upOrthoPolynomial_two` extracts the concrete `P₂ = x² - 1/9`.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

/-- A polynomial of degree `< n` annihilated by all monomials below
`n` is zero: it has zero squared mass. -/
theorem eq_zero_of_natDegree_lt_of_orthogonal (F : BoundedFabius)
    (hF : IsFabius F) {n : ℕ} {r : Polynomial ℝ}
    (hdeg : r.natDegree < n)
    (horth : ∀ j < n,
      ∫ x, r.eval x * x ^ j ∂(rvachevMeasure F) = 0) :
    r = 0 := by
  by_contra hne
  have hzero : ∫ x, r.eval x * r.eval x ∂(rvachevMeasure F) = 0 :=
    integral_mul_eval_eq_zero_of_forall_pow F hF horth hdeg
  have hzero' : ∫ x, r.eval x ^ 2 ∂(rvachevMeasure F) = 0 := by
    have hfun : (fun x : ℝ => r.eval x ^ 2) =
        fun x : ℝ => r.eval x * r.eval x := funext fun x => by ring
    rw [hfun]
    exact hzero
  exact absurd hzero' (ne_of_gt (integral_sq_eval_pos F hF hne))

/-- Degree-zero case of the recurrence: `x·P₀ = P₁`. -/
theorem upOrthoPolynomial_three_term_zero (F : BoundedFabius)
    (hF : IsFabius F) :
    Polynomial.X * upOrthoPolynomial F 0 = upOrthoPolynomial F 1 := by
  rw [upOrthoPolynomial_zero, upOrthoPolynomial_one F hF, mul_one]

/-- **The three-term recurrence**:
`x·P_{n+1} = P_{n+2} + (a_{n+1}/a_n)·P_n`, with `a_n` the Hankel
ratio `h_{n+1}/h_n` — the squared `L²`-norm of `P_n`. -/
theorem upOrthoPolynomial_three_term (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    Polynomial.X * upOrthoPolynomial F (n + 1) =
      upOrthoPolynomial F (n + 2) +
        Polynomial.C (hankelRatio F (n + 1) / hankelRatio F n) *
          upOrthoPolynomial F n := by
  set c : ℝ := hankelRatio F (n + 1) / hankelRatio F n with hc
  set r : Polynomial ℝ :=
    Polynomial.X * upOrthoPolynomial F (n + 1) -
      upOrthoPolynomial F (n + 2) -
      Polynomial.C c * upOrthoPolynomial F n with hr
  have hmonXP : (Polynomial.X * upOrthoPolynomial F (n + 1)).Monic :=
    Polynomial.monic_X.mul (upOrthoPolynomial_monic F hF (n + 1))
  have hdegXP : (Polynomial.X *
      upOrthoPolynomial F (n + 1)).natDegree = n + 2 := by
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero
      (upOrthoPolynomial_monic F hF (n + 1)).ne_zero,
      Polynomial.natDegree_X, natDegree_upOrthoPolynomial F hF (n + 1)]
  have hkey : r = 0 := by
    refine eq_zero_of_natDegree_lt_of_orthogonal F hF
      (n := n + 2) ?_ ?_
    · -- degree bound: the monic leading terms cancel
      have hcoeffs2 : ∀ m : ℕ, n + 2 ≤ m →
          (Polynomial.X * upOrthoPolynomial F (n + 1) -
            upOrthoPolynomial F (n + 2)).coeff m = 0 := by
        intro m hm
        rw [Polynomial.coeff_sub]
        rcases eq_or_lt_of_le hm with hEq | hlt
        · rw [← hEq]
          have h1 : (Polynomial.X *
              upOrthoPolynomial F (n + 1)).coeff (n + 2) = 1 := by
            have h := hmonXP.coeff_natDegree
            rwa [hdegXP] at h
          have h2 : (upOrthoPolynomial F (n + 2)).coeff (n + 2) = 1 := by
            have h :=
              (upOrthoPolynomial_monic F hF (n + 2)).coeff_natDegree
            rwa [natDegree_upOrthoPolynomial F hF (n + 2)] at h
          rw [h1, h2, sub_self]
        · have h1 : (Polynomial.X *
              upOrthoPolynomial F (n + 1)).coeff m = 0 := by
            refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
            rw [hdegXP]
            exact hlt
          have h2 : (upOrthoPolynomial F (n + 2)).coeff m = 0 := by
            refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
            rw [natDegree_upOrthoPolynomial F hF (n + 2)]
            exact hlt
          rw [h1, h2, sub_zero]
      have hdeg2 : (Polynomial.X * upOrthoPolynomial F (n + 1) -
          upOrthoPolynomial F (n + 2)).natDegree ≤ n + 1 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN =>
          hcoeffs2 N (by omega)
      have hdeg3 : (Polynomial.C c *
          upOrthoPolynomial F n).natDegree ≤ n :=
        le_trans (Polynomial.natDegree_C_mul_le _ _)
          (le_of_eq (natDegree_upOrthoPolynomial F hF n))
      have hrle : r.natDegree ≤ n + 1 := by
        rw [hr]
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        exact max_le hdeg2 (le_trans hdeg3 (by omega))
      omega
    · -- orthogonality below n+2
      intro j hj
      have hint1 : Integrable (fun x : ℝ =>
          (upOrthoPolynomial F (n + 1)).eval x * x ^ (j + 1))
          (rvachevMeasure F) := by
        have h := integrable_polynomial_eval_rvachevMeasure F hF
          (upOrthoPolynomial F (n + 1) * Polynomial.X ^ (j + 1))
        simpa [Polynomial.eval_mul, Polynomial.eval_pow] using h
      have hint2 : Integrable (fun x : ℝ =>
          (upOrthoPolynomial F (n + 2)).eval x * x ^ j)
          (rvachevMeasure F) := by
        have h := integrable_polynomial_eval_rvachevMeasure F hF
          (upOrthoPolynomial F (n + 2) * Polynomial.X ^ j)
        simpa [Polynomial.eval_mul, Polynomial.eval_pow] using h
      have hint3' : Integrable (fun x : ℝ =>
          (upOrthoPolynomial F n).eval x * x ^ j)
          (rvachevMeasure F) := by
        have h := integrable_polynomial_eval_rvachevMeasure F hF
          (upOrthoPolynomial F n * Polynomial.X ^ j)
        simpa [Polynomial.eval_mul, Polynomial.eval_pow] using h
      have hint3 : Integrable (fun x : ℝ =>
          c * ((upOrthoPolynomial F n).eval x * x ^ j))
          (rvachevMeasure F) := hint3'.const_mul c
      have hre : (fun x : ℝ => r.eval x * x ^ j) = fun x : ℝ =>
          (upOrthoPolynomial F (n + 1)).eval x * x ^ (j + 1) -
            (upOrthoPolynomial F (n + 2)).eval x * x ^ j -
            c * ((upOrthoPolynomial F n).eval x * x ^ j) := by
        funext x
        rw [hr, Polynomial.eval_sub, Polynomial.eval_sub,
          Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X, pow_succ]
        ring
      rw [hre, MeasureTheory.integral_sub (hint1.sub hint2) hint3,
        MeasureTheory.integral_sub hint1 hint2,
        MeasureTheory.integral_const_mul]
      rcases Nat.lt_or_ge j n with hjn | hjn
      · rw [integral_upOrthoPolynomial_mul_pow F hF
            (by omega : j + 1 < n + 1),
          integral_upOrthoPolynomial_mul_pow F hF
            (by omega : j < n + 2),
          integral_upOrthoPolynomial_mul_pow F hF hjn]
        ring
      · rcases eq_or_lt_of_le hjn with hEq | hgt
        · rw [← hEq,
            integral_upOrthoPolynomial_mul_pow_self F hF (n + 1),
            integral_upOrthoPolynomial_mul_pow F hF
              (by omega : n < n + 2),
            integral_upOrthoPolynomial_mul_pow_self F hF n, hc,
            div_mul_cancel₀ _ (ne_of_gt (hankelRatio_pos F hF n))]
          ring
        · have hj1 : j = n + 1 := by omega
          subst hj1
          rw [integral_upOrthoPolynomial_mul_pow_eq_zero_of_odd F hF
              (⟨n + 1, by ring⟩ : Odd (n + 1 + (n + 1 + 1))),
            integral_upOrthoPolynomial_mul_pow F hF
              (by omega : n + 1 < n + 2),
            integral_upOrthoPolynomial_mul_pow_eq_zero_of_odd F hF
              (⟨n, by ring⟩ : Odd (n + (n + 1)))]
          ring
  have h0 : Polynomial.X * upOrthoPolynomial F (n + 1) -
      upOrthoPolynomial F (n + 2) -
      Polynomial.C c * upOrthoPolynomial F n = 0 := by
    rw [← hr]
    exact hkey
  have h1 : Polynomial.X * upOrthoPolynomial F (n + 1) -
      upOrthoPolynomial F (n + 2) =
      Polynomial.C c * upOrthoPolynomial F n := sub_eq_zero.mp h0
  have h2 := sub_eq_iff_eq_add.mp h1
  rw [h2, add_comm]

/-- Pointwise form of the recurrence. -/
theorem upOrthoPolynomial_three_term_eval (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    x * (upOrthoPolynomial F (n + 1)).eval x =
      (upOrthoPolynomial F (n + 2)).eval x +
        (hankelRatio F (n + 1) / hankelRatio F n) *
          (upOrthoPolynomial F n).eval x := by
  have h := congrArg (Polynomial.eval x)
    (upOrthoPolynomial_three_term F hF n)
  simpa using h

/-- The concrete third polynomial: `P₂ = x² - 1/9`. -/
theorem upOrthoPolynomial_two (F : BoundedFabius) (hF : IsFabius F) :
    upOrthoPolynomial F 2 =
      Polynomial.X ^ 2 - Polynomial.C (1 / 9 : ℝ) := by
  have h := upOrthoPolynomial_three_term F hF 0
  rw [upOrthoPolynomial_one F hF, upOrthoPolynomial_zero,
    hankelRatio_one F hF, hankelRatio_zero F hF, mul_one] at h
  have h2 : upOrthoPolynomial F 2 =
      Polynomial.X * Polynomial.X -
        Polynomial.C ((1 / 9 : ℝ) / 1) := by
    rw [eq_sub_iff_add_eq]
    exact h.symm
  rw [h2]
  have hnum : ((1 / 9 : ℝ) / 1) = 1 / 9 := by norm_num
  rw [hnum, pow_two]

end Fabius
