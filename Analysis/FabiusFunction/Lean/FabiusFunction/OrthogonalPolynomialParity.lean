import FabiusFunction.OrthogonalPolynomialConstruction

/-!
# Parity of the up-measure's orthogonal polynomials

The up-measure is symmetric, so its monic orthogonal polynomials have
the parity of their degree.  The proof is the uniqueness
characterization at work: `(-1)^n·P_n(-X)` is again monic of degree
`n` and orthogonal to all lower monomials — the negation substitution
is measure-invariant — so it *is* `P_n`.

* `upOrthoPolynomial_comp_neg_X` — `P_n(-X) = (-1)^n·P_n`;
* `integral_upOrthoPolynomial_mul_pow_eq_zero_of_odd` — the pairings
  `∫ P_n(x)·x^j dμ_up` vanish whenever `n + j` is odd;
* `integral_mul_sq_upOrthoPolynomial_eq_zero` — `∫ x·P_n(x)² dμ_up = 0`:
  the Jacobi diagonal of the symmetric measure is identically zero.

These are the symmetry inputs of the three-term recurrence: the
`x·P_n`-expansion has no `P_n`-component, and the `j = n` pairing of
`x·P_n` against `x^n` costs nothing.
-/

set_option autoImplicit false

open MeasureTheory

namespace Fabius

/-- Monomial instance of the orthogonality relations. -/
theorem integral_upOrthoPolynomial_mul_pow (F : BoundedFabius)
    (hF : IsFabius F) {n j : ℕ} (hj : j < n) :
    ∫ x, (upOrthoPolynomial F n).eval x * x ^ j
      ∂(rvachevMeasure F) = 0 := by
  have h := integral_upOrthoPolynomial_mul_eval F hF n
    (Polynomial.X ^ j)
    (by simpa [Polynomial.natDegree_X_pow] using hj)
  simpa [Polynomial.eval_pow] using h

/-- **Parity**: the monic orthogonal polynomials of the symmetric
up-measure satisfy `P_n(-X) = (-1)^n·P_n`. -/
theorem upOrthoPolynomial_comp_neg_X (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    (upOrthoPolynomial F n).comp (-Polynomial.X) =
      Polynomial.C ((-1 : ℝ) ^ n) * upOrthoPolynomial F n := by
  have hcne : ((-1 : ℝ) ^ n) ≠ 0 :=
    pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)
  have hnegX : (-Polynomial.X : Polynomial ℝ).natDegree = 1 := by
    simp
  have hnegXlc : (-Polynomial.X : Polynomial ℝ).leadingCoeff = -1 := by
    simp
  have hqmonic : (Polynomial.C ((-1 : ℝ) ^ n) *
      (upOrthoPolynomial F n).comp (-Polynomial.X)).Monic := by
    have hlc : (Polynomial.C ((-1 : ℝ) ^ n) *
        (upOrthoPolynomial F n).comp (-Polynomial.X)).leadingCoeff
        = 1 := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        Polynomial.leadingCoeff_comp (by rw [hnegX]; exact one_ne_zero),
        (upOrthoPolynomial_monic F hF n).leadingCoeff, hnegXlc,
        natDegree_upOrthoPolynomial F hF n, one_mul, ← pow_add]
      exact Even.neg_one_pow ⟨n, rfl⟩
    exact hlc
  have hqdeg : (Polynomial.C ((-1 : ℝ) ^ n) *
      (upOrthoPolynomial F n).comp (-Polynomial.X)).natDegree = n := by
    rw [Polynomial.natDegree_C_mul hcne, Polynomial.natDegree_comp,
      hnegX, mul_one, natDegree_upOrthoPolynomial F hF n]
  have hqorth : ∀ j < n, ∫ x, (Polynomial.C ((-1 : ℝ) ^ n) *
      (upOrthoPolynomial F n).comp (-Polynomial.X)).eval x * x ^ j
      ∂(rvachevMeasure F) = 0 := by
    intro j hj
    have hqe : (fun x : ℝ => (Polynomial.C ((-1 : ℝ) ^ n) *
        (upOrthoPolynomial F n).comp (-Polynomial.X)).eval x * x ^ j) =
        fun x : ℝ => (-1 : ℝ) ^ n *
          ((upOrthoPolynomial F n).eval (-x) * x ^ j) := by
      funext x
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_neg, Polynomial.eval_X]
      ring
    rw [hqe, MeasureTheory.integral_const_mul]
    have hswap : ∫ x, (upOrthoPolynomial F n).eval (-x) * x ^ j
        ∂(rvachevMeasure F) =
        ∫ x, (upOrthoPolynomial F n).eval x * (-x) ^ j
        ∂(rvachevMeasure F) := by
      have h := integral_comp_neg_rvachevMeasure F hF
        (fun y : ℝ => (upOrthoPolynomial F n).eval y * (-y) ^ j)
      simpa [neg_neg] using h
    rw [hswap]
    have hpull : (fun x : ℝ =>
        (upOrthoPolynomial F n).eval x * (-x) ^ j) =
        fun x : ℝ => (-1 : ℝ) ^ j *
          ((upOrthoPolynomial F n).eval x * x ^ j) := by
      funext x
      rw [neg_pow]
      ring
    rw [hpull, MeasureTheory.integral_const_mul,
      integral_upOrthoPolynomial_mul_pow F hF hj, mul_zero, mul_zero]
  have hq := eq_upOrthoPolynomial_of_monic_of_orthogonal F hF
    hqmonic hqdeg hqorth
  have hsq : Polynomial.C ((-1 : ℝ) ^ n) *
      Polynomial.C ((-1 : ℝ) ^ n) = 1 := by
    rw [← Polynomial.C_mul, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩,
      Polynomial.C_1]
  calc (upOrthoPolynomial F n).comp (-Polynomial.X)
      = (Polynomial.C ((-1 : ℝ) ^ n) * Polynomial.C ((-1 : ℝ) ^ n)) *
          (upOrthoPolynomial F n).comp (-Polynomial.X) := by
        rw [hsq, one_mul]
    _ = Polynomial.C ((-1 : ℝ) ^ n) *
          (Polynomial.C ((-1 : ℝ) ^ n) *
            (upOrthoPolynomial F n).comp (-Polynomial.X)) := by
        ring
    _ = Polynomial.C ((-1 : ℝ) ^ n) * upOrthoPolynomial F n := by
        rw [hq]

/-- Pointwise parity: `P_n(-x) = (-1)^n·P_n(x)`. -/
theorem upOrthoPolynomial_eval_neg (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) (x : ℝ) :
    (upOrthoPolynomial F n).eval (-x) =
      (-1 : ℝ) ^ n * (upOrthoPolynomial F n).eval x := by
  have h := congrArg (Polynomial.eval x)
    (upOrthoPolynomial_comp_neg_X F hF n)
  rwa [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at h

/-- Parity kills the odd pairings: `∫ P_n(x)·x^j dμ_up = 0` whenever
`n + j` is odd — in particular for `j = n + 1` and (when `n ≥ 1`) for
`j = n - 1` shifted by one. -/
theorem integral_upOrthoPolynomial_mul_pow_eq_zero_of_odd
    (F : BoundedFabius) (hF : IsFabius F) {n j : ℕ}
    (hodd : Odd (n + j)) :
    ∫ x, (upOrthoPolynomial F n).eval x * x ^ j
      ∂(rvachevMeasure F) = 0 := by
  have hpt : ∀ x : ℝ,
      (upOrthoPolynomial F n).eval (-x) * (-x) ^ j =
        -((upOrthoPolynomial F n).eval x * x ^ j) := by
    intro x
    have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ j = -1 := by
      rw [← pow_add]
      exact Odd.neg_one_pow hodd
    rw [upOrthoPolynomial_eval_neg F hF n x, neg_pow]
    linear_combination
      ((upOrthoPolynomial F n).eval x * x ^ j) * hsign
  have hneg := integral_comp_neg_rvachevMeasure F hF
    (fun x : ℝ => (upOrthoPolynomial F n).eval x * x ^ j)
  have hI : ∫ x, (upOrthoPolynomial F n).eval x * x ^ j
      ∂(rvachevMeasure F) =
      -∫ x, (upOrthoPolynomial F n).eval x * x ^ j
      ∂(rvachevMeasure F) := by
    conv_lhs => rw [← hneg]
    rw [← MeasureTheory.integral_neg]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => hpt x)
  linarith [hI]

/-- **The Jacobi diagonal vanishes**: `∫ x·P_n(x)² dμ_up = 0` — the
recurrence of a symmetric measure has no `b_n`-terms. -/
theorem integral_mul_sq_upOrthoPolynomial_eq_zero (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    ∫ x, x * (upOrthoPolynomial F n).eval x ^ 2
      ∂(rvachevMeasure F) = 0 := by
  have hpt : ∀ x : ℝ,
      (-x) * (upOrthoPolynomial F n).eval (-x) ^ 2 =
        -(x * (upOrthoPolynomial F n).eval x ^ 2) := by
    intro x
    rw [upOrthoPolynomial_eval_neg F hF n x, mul_pow, ← pow_mul,
      Even.neg_one_pow ⟨n, by ring⟩]
    ring
  have hneg := integral_comp_neg_rvachevMeasure F hF
    (fun x : ℝ => x * (upOrthoPolynomial F n).eval x ^ 2)
  have hI : ∫ x, x * (upOrthoPolynomial F n).eval x ^ 2
      ∂(rvachevMeasure F) =
      -∫ x, x * (upOrthoPolynomial F n).eval x ^ 2
      ∂(rvachevMeasure F) := by
    conv_lhs => rw [← hneg]
    rw [← MeasureTheory.integral_neg]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => hpt x)
  linarith [hI]

end Fabius
