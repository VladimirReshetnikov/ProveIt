import FabiusFunction.FabiusLegendreSeries
import Mathlib.Order.Interval.Set.Infinite

/-!
# Least-squares optimality of the Rvachev--Legendre partial sums

The finite Fourier--Legendre projection through degree `N` is characterized
by a Pythagorean identity for the unweighted squared `L²[-1,1]` error.  We
then specialize this generic fact to Rvachev's even `up` function.  The
generic theory only assumes continuity on the closed integration interval,
and shows in particular that projection fixes every polynomial already in
the degree class.

If

`S_N = ∑ n ∈ range (N + 1), u_n P_(2n)`,

then `S_N` is the unique least-squares minimizer among all real polynomials
of degree at most `2N + 1`.  This is slightly stronger than optimality in its
visible degree class `≤ 2N`: the additional odd coefficient is zero because
`up` is even.
-/

set_option autoImplicit false

open scoped BigOperators Interval Polynomial
open Set Finset MeasureTheory Polynomial

namespace Fabius

noncomputable section

/-! ## Generic finite Fourier--Legendre projection -/

/-- The degree-`N` Fourier--Legendre projection polynomial of `f`. -/
noncomputable def legendreProjectionPolynomial
    (f : ℝ → ℝ) (N : ℕ) : ℝ[X] :=
  ∑ n ∈ range (N + 1),
    legendreSeriesCoefficientOf f
      (fun x : ℝ ↦ (legendrePolynomial n).eval x) n •
      legendrePolynomial n

/-- Evaluation of the degree-`N` Fourier--Legendre projection: the value at
`x` is the sum over `n` in `range (N + 1)` of the normalized coefficient of
index `n` times `P_n x`.  Used as a rewrite in
`integral_legendreProjectionPolynomial_mul_legendre`. -/
@[simp]
theorem eval_legendreProjectionPolynomial
    (f : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    (legendreProjectionPolynomial f N).eval x =
      ∑ n ∈ range (N + 1),
        legendreSeriesCoefficientOf f
          (fun y : ℝ ↦ (legendrePolynomial n).eval y) n *
          (legendrePolynomial n).eval x := by
  simp only [legendreProjectionPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul]

/-- The Fourier--Legendre projection has degree at most `N`. -/
theorem legendreProjectionPolynomial_mem_degreeLE
    (f : ℝ → ℝ) (N : ℕ) :
    legendreProjectionPolynomial f N ∈ Polynomial.degreeLE ℝ N := by
  rw [legendreProjectionPolynomial]
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  rw [Polynomial.mem_degreeLE]
  simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn)

/-- Squared unweighted `L²[-1,1]` error of a polynomial approximation. -/
noncomputable def legendreSquaredError
    (f : ℝ → ℝ) (p : ℝ[X]) : ℝ :=
  ∫ x in (-1 : ℝ)..1, (f x - p.eval x) ^ 2

private theorem integral_legendreProjectionPolynomial_mul_legendre
    (f : ℝ → ℝ) (N i : ℕ) (hi : i ≤ N) :
    (∫ x in (-1 : ℝ)..1,
      (legendreProjectionPolynomial f N).eval x *
        (legendrePolynomial i).eval x) =
      ∫ x in (-1 : ℝ)..1,
        f x * (legendrePolynomial i).eval x := by
  rw [show
      (∫ x in (-1 : ℝ)..1,
        (legendreProjectionPolynomial f N).eval x *
          (legendrePolynomial i).eval x) =
        ∑ n ∈ range (N + 1),
          legendreSeriesCoefficientOf f
            (fun y : ℝ ↦ (legendrePolynomial n).eval y) n *
            (∫ x in (-1 : ℝ)..1,
              (legendrePolynomial n).eval x *
                (legendrePolynomial i).eval x) by
    rw [show
        (∫ x in (-1 : ℝ)..1,
          (legendreProjectionPolynomial f N).eval x *
            (legendrePolynomial i).eval x) =
          ∫ x in (-1 : ℝ)..1,
            ∑ n ∈ range (N + 1),
              legendreSeriesCoefficientOf f
                (fun y : ℝ ↦ (legendrePolynomial n).eval y) n *
                ((legendrePolynomial n).eval x *
                  (legendrePolynomial i).eval x) by
      apply intervalIntegral.integral_congr
      intro x _hx
      change (legendreProjectionPolynomial f N).eval x *
        (legendrePolynomial i).eval x = _
      rw [eval_legendreProjectionPolynomial, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_const_mul]
    · intro n hn
      apply Continuous.intervalIntegrable
      fun_prop]
  rw [sum_eq_single_of_mem i (by simpa using Nat.lt_succ_of_le hi)]
  · rw [integral_eval_legendrePolynomial_mul, if_pos rfl]
    dsimp [legendreSeriesCoefficientOf]
    have hden : (((2 * i + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  · intro n hn hne
    rw [integral_eval_legendrePolynomial_mul, if_neg hne, mul_zero]

/-- The residual of the degree-`N` Fourier--Legendre projection is
orthogonal to every polynomial of degree at most `N`. -/
theorem integral_sub_projection_mul_polynomial_eq_zero_of_continuousOn
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) :
    (∫ x in (-1 : ℝ)..1,
      (f x - (legendreProjectionPolynomial f N).eval x) * q.eval x) = 0 := by
  let L : Polynomial.Sequence ℝ := {
    elems' := legendrePolynomial
    degree_eq' := degree_legendrePolynomial
  }
  let T : ℝ[X] →ₗ[ℝ] ℝ := {
    toFun := fun p ↦ ∫ x in (-1 : ℝ)..1,
      (f x - (legendreProjectionPolynomial f N).eval x) * p.eval x
    map_add' := by
      intro p q
      have hp : IntervalIntegrable (fun x : ℝ ↦
          (f x - (legendreProjectionPolynomial f N).eval x) * p.eval x)
          volume (-1) 1 := by
        exact ((hf.sub
          (legendreProjectionPolynomial f N).continuous.continuousOn).mul
            p.continuous.continuousOn).intervalIntegrable_of_Icc (by norm_num)
      have hq : IntervalIntegrable (fun x : ℝ ↦
          (f x - (legendreProjectionPolynomial f N).eval x) * q.eval x)
          volume (-1) 1 := by
        exact ((hf.sub
          (legendreProjectionPolynomial f N).continuous.continuousOn).mul
            q.continuous.continuousOn).intervalIntegrable_of_Icc (by norm_num)
      rw [← intervalIntegral.integral_add hp hq]
      apply intervalIntegral.integral_congr
      intro x _hx
      simp only [eval_add]
      ring
    map_smul' := by
      intro c p
      rw [RingHom.id_apply]
      rw [show (∫ x in (-1 : ℝ)..1,
          (f x - (legendreProjectionPolynomial f N).eval x) *
            (c • p).eval x) =
          ∫ x in (-1 : ℝ)..1,
            c * ((f x - (legendreProjectionPolynomial f N).eval x) *
              p.eval x) by
        apply intervalIntegral.integral_congr
        intro x _hx
        simp only [eval_smul, smul_eq_mul]
        ring]
      rw [intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]
  }
  have hunit : ∀ i ≤ N, IsUnit (L i).leadingCoeff := by
    intro i hi
    rw [isUnit_iff_ne_zero]
    exact Polynomial.leadingCoeff_ne_zero.mpr (L.ne_zero i)
  have hspan : Submodule.span ℝ (L '' Set.Iic N) = Polynomial.degreeLE ℝ N :=
    L.span_degreeLE hunit
  have hrange : L '' Set.Iic N ⊆ T.ker := by
    rintro p ⟨i, hi, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (∫ x in (-1 : ℝ)..1,
      (f x - (legendreProjectionPolynomial f N).eval x) *
        (legendrePolynomial i).eval x) = 0
    have hfInt : IntervalIntegrable
        (fun x : ℝ ↦ f x * (legendrePolynomial i).eval x) volume (-1) 1 :=
      (hf.mul (legendrePolynomial_contDiff i).continuous.continuousOn)
        |>.intervalIntegrable_of_Icc (by norm_num)
    have hsInt : IntervalIntegrable
        (fun x : ℝ ↦ (legendreProjectionPolynomial f N).eval x *
          (legendrePolynomial i).eval x) volume (-1) 1 :=
      ((legendreProjectionPolynomial f N).continuous.mul
        (legendrePolynomial_contDiff i).continuous).intervalIntegrable _ _
    rw [show (∫ x in (-1 : ℝ)..1,
        (f x - (legendreProjectionPolynomial f N).eval x) *
          (legendrePolynomial i).eval x) =
        (∫ x in (-1 : ℝ)..1, f x * (legendrePolynomial i).eval x) -
          ∫ x in (-1 : ℝ)..1,
            (legendreProjectionPolynomial f N).eval x *
              (legendrePolynomial i).eval x by
      rw [← intervalIntegral.integral_sub hfInt hsInt]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring]
    rw [integral_legendreProjectionPolynomial_mul_legendre f N i hi, sub_self]
  have hspanKer : Polynomial.degreeLE ℝ N ≤ T.ker := by
    rw [← hspan]
    exact Submodule.span_le.mpr hrange
  exact LinearMap.mem_ker.mp (hspanKer (Polynomial.mem_degreeLE.mpr hq))

/-- Compatibility form of
`integral_sub_projection_mul_polynomial_eq_zero_of_continuousOn` for a
globally continuous function. -/
theorem integral_sub_projection_mul_polynomial_eq_zero
    (f : ℝ → ℝ) (hf : Continuous f) (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) :
    (∫ x in (-1 : ℝ)..1,
      (f x - (legendreProjectionPolynomial f N).eval x) * q.eval x) = 0 :=
  integral_sub_projection_mul_polynomial_eq_zero_of_continuousOn
    f hf.continuousOn N q hq

/-- Pythagorean identity for the degree-`N` Fourier--Legendre projection. -/
theorem legendreSquaredError_eq_add_of_continuousOn
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) :
    legendreSquaredError f q =
      legendreSquaredError f (legendreProjectionPolynomial f N) +
        (∫ x in (-1 : ℝ)..1,
          ((legendreProjectionPolynomial f N).eval x - q.eval x) ^ 2) := by
  let S := legendreProjectionPolynomial f N
  have hS : S ∈ Polynomial.degreeLE ℝ N := by
    simpa [S] using legendreProjectionPolynomial_mem_degreeLE f N
  have hqmem : q ∈ Polynomial.degreeLE ℝ N :=
    Polynomial.mem_degreeLE.mpr hq
  have hcross := integral_sub_projection_mul_polynomial_eq_zero_of_continuousOn
    f hf N (S - q) (Polynomial.mem_degreeLE.mp (Submodule.sub_mem _ hS hqmem))
  change (∫ x in (-1 : ℝ)..1, (f x - q.eval x) ^ 2) =
    (∫ x in (-1 : ℝ)..1, (f x - S.eval x) ^ 2) +
      ∫ x in (-1 : ℝ)..1, (S.eval x - q.eval x) ^ 2
  have hc1 : ContinuousOn (fun x : ℝ ↦ (f x - S.eval x) ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (hf.sub S.continuous.continuousOn).pow 2
  have hc2 : ContinuousOn (fun x : ℝ ↦
      2 * ((f x - S.eval x) * (S.eval x - q.eval x)))
      (Icc (-1 : ℝ) 1) :=
    continuousOn_const.mul ((hf.sub S.continuous.continuousOn).mul
      (S.continuous.continuousOn.sub q.continuous.continuousOn))
  have hc3 : ContinuousOn (fun x : ℝ ↦ (S.eval x - q.eval x) ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (S.continuous.continuousOn.sub q.continuous.continuousOn).pow 2
  rw [show (∫ x in (-1 : ℝ)..1, (f x - q.eval x) ^ 2) =
      ∫ x in (-1 : ℝ)..1,
        ((f x - S.eval x) ^ 2 +
          2 * ((f x - S.eval x) * (S.eval x - q.eval x)) +
          (S.eval x - q.eval x) ^ 2) by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring]
  have hcross' : (∫ x in (-1 : ℝ)..1,
      (f x - S.eval x) * (S.eval x - q.eval x)) = 0 := by
    simpa [S, eval_sub] using hcross
  have htwocross : (∫ x in (-1 : ℝ)..1,
      2 * ((f x - S.eval x) * (S.eval x - q.eval x))) = 0 := by
    rw [intervalIntegral.integral_const_mul, hcross', mul_zero]
  have haddOuter :
      (∫ x in (-1 : ℝ)..1,
        ((f x - S.eval x) ^ 2 +
          2 * ((f x - S.eval x) * (S.eval x - q.eval x))) +
          (S.eval x - q.eval x) ^ 2) =
        (∫ x in (-1 : ℝ)..1,
          (f x - S.eval x) ^ 2 +
            2 * ((f x - S.eval x) * (S.eval x - q.eval x))) +
        ∫ x in (-1 : ℝ)..1, (S.eval x - q.eval x) ^ 2 := by
    simpa only [Pi.add_apply] using intervalIntegral.integral_add (μ := volume)
      ((hc1.add hc2).intervalIntegrable_of_Icc (by norm_num))
      (hc3.intervalIntegrable_of_Icc (by norm_num))
  have haddInner :
      (∫ x in (-1 : ℝ)..1,
        (f x - S.eval x) ^ 2 +
          2 * ((f x - S.eval x) * (S.eval x - q.eval x))) =
        (∫ x in (-1 : ℝ)..1, (f x - S.eval x) ^ 2) +
        ∫ x in (-1 : ℝ)..1,
          2 * ((f x - S.eval x) * (S.eval x - q.eval x)) := by
    simpa only [Pi.add_apply] using intervalIntegral.integral_add (μ := volume)
      (hc1.intervalIntegrable_of_Icc (by norm_num))
      (hc2.intervalIntegrable_of_Icc (by norm_num))
  rw [haddOuter, haddInner, htwocross]
  ring

/-- Compatibility form of `legendreSquaredError_eq_add_of_continuousOn` for
a globally continuous function. -/
theorem legendreSquaredError_eq_add
    (f : ℝ → ℝ) (hf : Continuous f) (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) :
    legendreSquaredError f q =
      legendreSquaredError f (legendreProjectionPolynomial f N) +
        (∫ x in (-1 : ℝ)..1,
          ((legendreProjectionPolynomial f N).eval x - q.eval x) ^ 2) :=
  legendreSquaredError_eq_add_of_continuousOn f hf.continuousOn N q hq

/-- A nonzero polynomial difference has strictly positive squared integral on
`[-1,1]`. -/
theorem integral_sq_eval_sub_pos {p q : ℝ[X]} (hpq : p ≠ q) :
    0 < ∫ x in (-1 : ℝ)..1, (p.eval x - q.eval x) ^ 2 := by
  have hexists : ∃ x ∈ Icc (-1 : ℝ) 1, p.eval x ≠ q.eval x := by
    by_contra h
    apply hpq
    apply Polynomial.eq_of_infinite_eval_eq p q
    exact (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono (by
      intro x hx
      by_contra hne
      exact h ⟨x, hx, hne⟩)
  apply intervalIntegral.integral_pos (by norm_num)
  · fun_prop
  · intro x hx
    positivity
  · obtain ⟨x, hx, hne⟩ := hexists
    exact ⟨x, hx, sq_pos_of_ne_zero (sub_ne_zero.mpr hne)⟩

/-- The Fourier--Legendre projection minimizes squared `L²[-1,1]` error
among all polynomials of degree at most `N`. -/
theorem legendreProjectionPolynomial_least_squares_of_continuousOn
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) :
    legendreSquaredError f (legendreProjectionPolynomial f N) ≤
      legendreSquaredError f q := by
  rw [legendreSquaredError_eq_add_of_continuousOn f hf N q hq]
  exact le_add_of_nonneg_right
    (intervalIntegral.integral_nonneg (by norm_num) fun _x _hx ↦ sq_nonneg _)

/-- Compatibility form of
`legendreProjectionPolynomial_least_squares_of_continuousOn` for a globally
continuous function. -/
theorem legendreProjectionPolynomial_least_squares
    (f : ℝ → ℝ) (hf : Continuous f) (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) :
    legendreSquaredError f (legendreProjectionPolynomial f N) ≤
      legendreSquaredError f q :=
  legendreProjectionPolynomial_least_squares_of_continuousOn
    f hf.continuousOn N q hq

/-- Equality in the least-squares inequality occurs only at the projection
polynomial. -/
theorem legendreSquaredError_eq_projection_iff_of_continuousOn
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) :
    legendreSquaredError f q =
        legendreSquaredError f (legendreProjectionPolynomial f N) ↔
      q = legendreProjectionPolynomial f N := by
  constructor
  · intro heq
    by_contra hne
    have hpos : 0 < ∫ x in (-1 : ℝ)..1,
        ((legendreProjectionPolynomial f N).eval x - q.eval x) ^ 2 :=
      integral_sq_eval_sub_pos (Ne.symm hne)
    have hpyth := legendreSquaredError_eq_add_of_continuousOn f hf N q hq
    linarith
  · rintro rfl
    rfl

/-- Compatibility form of
`legendreSquaredError_eq_projection_iff_of_continuousOn` for a globally
continuous function. -/
theorem legendreSquaredError_eq_projection_iff
    (f : ℝ → ℝ) (hf : Continuous f) (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) :
    legendreSquaredError f q =
        legendreSquaredError f (legendreProjectionPolynomial f N) ↔
      q = legendreProjectionPolynomial f N :=
  legendreSquaredError_eq_projection_iff_of_continuousOn
    f hf.continuousOn N q hq

/-- Every distinct degree-`N` competitor has strictly larger squared error. -/
theorem legendreProjectionPolynomial_strict_least_squares_of_continuousOn
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) (hne : q ≠ legendreProjectionPolynomial f N) :
    legendreSquaredError f (legendreProjectionPolynomial f N) <
      legendreSquaredError f q := by
  have hpyth := legendreSquaredError_eq_add_of_continuousOn f hf N q hq
  have hpos : 0 < ∫ x in (-1 : ℝ)..1,
      ((legendreProjectionPolynomial f N).eval x - q.eval x) ^ 2 :=
    integral_sq_eval_sub_pos (Ne.symm hne)
  linarith

/-- Compatibility form of
`legendreProjectionPolynomial_strict_least_squares_of_continuousOn` for a
globally continuous function. -/
theorem legendreProjectionPolynomial_strict_least_squares
    (f : ℝ → ℝ) (hf : Continuous f) (N : ℕ) (q : ℝ[X])
    (hq : q.degree ≤ N) (hne : q ≠ legendreProjectionPolynomial f N) :
    legendreSquaredError f (legendreProjectionPolynomial f N) <
      legendreSquaredError f q :=
  legendreProjectionPolynomial_strict_least_squares_of_continuousOn
    f hf.continuousOn N q hq hne

/-- The degree-`N` Fourier--Legendre projection fixes every polynomial of
degree at most `N`. -/
theorem legendreProjectionPolynomial_eval_eq_self
    (N : ℕ) (q : ℝ[X]) (hq : q.degree ≤ N) :
    legendreProjectionPolynomial (fun x : ℝ ↦ q.eval x) N = q := by
  let f : ℝ → ℝ := fun x ↦ q.eval x
  have hf : ContinuousOn f (Icc (-1 : ℝ) 1) := q.continuous.continuousOn
  have hqError : legendreSquaredError f q = 0 := by
    simp [legendreSquaredError, f]
  have hleast := legendreProjectionPolynomial_least_squares_of_continuousOn
    f hf N q hq
  have hprojectionNonneg :
      0 ≤ legendreSquaredError f (legendreProjectionPolynomial f N) := by
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _x _hx ↦ sq_nonneg _)
  have hprojectionError :
      legendreSquaredError f (legendreProjectionPolynomial f N) = 0 := by
    rw [hqError] at hleast
    exact le_antisymm hleast hprojectionNonneg
  symm
  apply (legendreSquaredError_eq_projection_iff_of_continuousOn
    f hf N q hq).mp
  rw [hqError, hprojectionError]

/-! ## The even Rvachev partial sums -/

/-- The displayed partial sum `∑ n ≤ N, u_n P_(2n)`. -/
noncomputable def rvachevLegendrePartialSumPolynomial
    (F : BoundedFabius) (N : ℕ) : ℝ[X] :=
  ∑ n ∈ range (N + 1),
    C (rvachevLegendreCoefficient F n) * legendrePolynomial (2 * n)

/-- Evaluation of the `N`-th even Rvachev--Legendre partial sum: the value
at `x` is the sum over `n` in `range (N + 1)` of
`rvachevLegendreCoefficient F n` times `P_(2n) x`.  This is a pure
`Polynomial.eval` computation; no hypothesis on `F` beyond `BoundedFabius`
enters. -/
@[simp]
theorem eval_rvachevLegendrePartialSumPolynomial
    (F : BoundedFabius) (N : ℕ) (x : ℝ) :
    (rvachevLegendrePartialSumPolynomial F N).eval x =
      ∑ n ∈ range (N + 1),
        rvachevLegendreCoefficient F n *
          (legendrePolynomial (2 * n)).eval x := by
  simp only [rvachevLegendrePartialSumPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]

/-- The visible degree of the `N`-th even partial sum is at most `2N`. -/
theorem rvachevLegendrePartialSumPolynomial_natDegree_le
    (F : BoundedFabius) (N : ℕ) :
    (rvachevLegendrePartialSumPolynomial F N).natDegree ≤ 2 * N := by
  rw [Polynomial.natDegree_le_iff_degree_le]
  rw [rvachevLegendrePartialSumPolynomial]
  apply Polynomial.mem_degreeLE.mp
  apply Submodule.sum_mem (Polynomial.degreeLE ℝ (2 * N))
  intro n hn
  apply Polynomial.mem_degreeLE.mpr
  have hnat : (C (rvachevLegendreCoefficient F n) *
      legendrePolynomial (2 * n)).natDegree ≤ 2 * N :=
    (Polynomial.natDegree_C_mul_le
    (rvachevLegendreCoefficient F n) (legendrePolynomial (2 * n))).trans (by
    rw [natDegree_legendrePolynomial]
    exact Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    Polynomial.natDegree_le_iff_degree_le.mp hnat

private noncomputable def rvachevFullLegendrePartialSumPolynomial
    (F : BoundedFabius) (N : ℕ) : ℝ[X] :=
  ∑ n ∈ range (N + 1),
    C (rvachevFullLegendreCoefficient F n) * legendrePolynomial n

private theorem legendreProjectionPolynomial_rvachevUp
    (F : BoundedFabius) (N : ℕ) :
    legendreProjectionPolynomial (rvachevUp F) N =
      rvachevFullLegendrePartialSumPolynomial F N := by
  simp only [legendreProjectionPolynomial,
    rvachevFullLegendrePartialSumPolynomial,
    legendreSeriesCoefficientOf_rvachevUp, smul_eq_C_mul]

private theorem rvachevFullLegendrePartialSumPolynomial_two_mul
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    rvachevFullLegendrePartialSumPolynomial F (2 * N) =
      rvachevLegendrePartialSumPolynomial F N := by
  induction N with
  | zero =>
      simp only [rvachevFullLegendrePartialSumPolynomial,
        rvachevLegendrePartialSumPolynomial, mul_zero, zero_add, range_one,
        sum_singleton]
      rw [rvachevFullLegendreCoefficient_even_eq F 0]
  | succ N ih =>
      calc
        rvachevFullLegendrePartialSumPolynomial F (2 * (N + 1)) =
            rvachevFullLegendrePartialSumPolynomial F (2 * N) +
              C (rvachevFullLegendreCoefficient F (2 * N + 1)) *
                legendrePolynomial (2 * N + 1) +
              C (rvachevFullLegendreCoefficient F (2 * N + 2)) *
                legendrePolynomial (2 * N + 2) := by
          rw [rvachevFullLegendrePartialSumPolynomial]
          rw [show 2 * (N + 1) + 1 = (2 * N + 1) + 2 by omega,
            sum_range_succ, sum_range_succ]
          rfl
        _ = rvachevLegendrePartialSumPolynomial F N +
              C (rvachevLegendreCoefficient F (N + 1)) *
                legendrePolynomial (2 * (N + 1)) := by
          rw [ih, rvachevFullLegendreCoefficient_odd_eq_zero F hF N,
            show 2 * N + 2 = 2 * (N + 1) by omega,
            rvachevFullLegendreCoefficient_even_eq F (N + 1)]
          simp
        _ = rvachevLegendrePartialSumPolynomial F (N + 1) := by
          symm
          change (∑ n ∈ range (N + 2),
              C (rvachevLegendreCoefficient F n) * legendrePolynomial (2 * n)) =
            (∑ n ∈ range (N + 1),
              C (rvachevLegendreCoefficient F n) * legendrePolynomial (2 * n)) +
              C (rvachevLegendreCoefficient F (N + 1)) *
                legendrePolynomial (2 * (N + 1))
          rw [sum_range_succ]

/-- Because the next odd coefficient vanishes, the even partial sum through
`P_(2N)` is the full Fourier--Legendre projection through degree `2N + 1`. -/
theorem legendreProjectionPolynomial_rvachevUp_two_mul_add_one
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    legendreProjectionPolynomial (rvachevUp F) (2 * N + 1) =
      rvachevLegendrePartialSumPolynomial F N := by
  rw [legendreProjectionPolynomial_rvachevUp]
  calc
    rvachevFullLegendrePartialSumPolynomial F (2 * N + 1) =
        rvachevFullLegendrePartialSumPolynomial F (2 * N) +
          C (rvachevFullLegendreCoefficient F (2 * N + 1)) *
            legendrePolynomial (2 * N + 1) := by
      simp only [rvachevFullLegendrePartialSumPolynomial]
      rw [sum_range_succ]
    _ = rvachevLegendrePartialSumPolynomial F N := by
      rw [rvachevFullLegendrePartialSumPolynomial_two_mul F hF N,
        rvachevFullLegendreCoefficient_odd_eq_zero F hF N]
      simp

/-- The squared approximation error for Rvachev's `up` function. -/
noncomputable def rvachevLegendreSquaredError
    (F : BoundedFabius) (p : ℝ[X]) : ℝ :=
  legendreSquaredError (rvachevUp F) p

/-- The residual of the displayed partial sum is orthogonal to every
polynomial of degree at most `2N + 1`. -/
theorem integral_rvachevUp_sub_partialSum_mul_polynomial_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) (q : ℝ[X])
    (hq : q.natDegree ≤ 2 * N + 1) :
    (∫ x in (-1 : ℝ)..1,
      (rvachevUp F x -
        (rvachevLegendrePartialSumPolynomial F N).eval x) * q.eval x) = 0 := by
  have h := integral_sub_projection_mul_polynomial_eq_zero_of_continuousOn
    (rvachevUp F) (rvachev_contDiff F hF).continuous.continuousOn (2 * N + 1) q
    (Polynomial.natDegree_le_iff_degree_le.mp hq)
  rw [legendreProjectionPolynomial_rvachevUp_two_mul_add_one F hF N] at h
  exact h

/-- Exact Pythagorean decomposition of the squared error. -/
theorem rvachevLegendrePartialSum_pythagorean
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) (q : ℝ[X])
    (hq : q.natDegree ≤ 2 * N + 1) :
    rvachevLegendreSquaredError F q =
      rvachevLegendreSquaredError F
          (rvachevLegendrePartialSumPolynomial F N) +
        (∫ x in (-1 : ℝ)..1,
          ((rvachevLegendrePartialSumPolynomial F N).eval x - q.eval x) ^ 2) := by
  have h := legendreSquaredError_eq_add_of_continuousOn
    (rvachevUp F) (rvachev_contDiff F hF).continuous.continuousOn (2 * N + 1) q
    (Polynomial.natDegree_le_iff_degree_le.mp hq)
  rw [legendreProjectionPolynomial_rvachevUp_two_mul_add_one F hF N] at h
  exact h

/-- Each displayed partial sum is a least-squares best approximation among
all real polynomials of degree at most `2N + 1`, and hence among those of
degree at most its visible degree `2N`. -/
theorem rvachevLegendrePartialSum_least_squares
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) (q : ℝ[X])
    (hq : q.natDegree ≤ 2 * N + 1) :
    rvachevLegendreSquaredError F
        (rvachevLegendrePartialSumPolynomial F N) ≤
      rvachevLegendreSquaredError F q := by
  rw [rvachevLegendrePartialSum_pythagorean F hF N q hq]
  exact le_add_of_nonneg_right
    (intervalIntegral.integral_nonneg (by norm_num) fun _x _hx ↦ sq_nonneg _)

/-- A distinct competitor of degree at most `2N + 1` has strictly larger
squared error. -/
theorem rvachevLegendrePartialSum_strict_least_squares
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) (q : ℝ[X])
    (hq : q.natDegree ≤ 2 * N + 1)
    (hne : q ≠ rvachevLegendrePartialSumPolynomial F N) :
    rvachevLegendreSquaredError F
        (rvachevLegendrePartialSumPolynomial F N) <
      rvachevLegendreSquaredError F q := by
  have hpyth := rvachevLegendrePartialSum_pythagorean F hF N q hq
  have hpos : 0 < ∫ x in (-1 : ℝ)..1,
      ((rvachevLegendrePartialSumPolynomial F N).eval x - q.eval x) ^ 2 :=
    integral_sq_eval_sub_pos (Ne.symm hne)
  linarith

/-- Equality of errors characterizes the displayed partial sum. -/
theorem rvachevLegendrePartialSum_error_eq_iff
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) (q : ℝ[X])
    (hq : q.natDegree ≤ 2 * N + 1) :
    rvachevLegendreSquaredError F q =
        rvachevLegendreSquaredError F
          (rvachevLegendrePartialSumPolynomial F N) ↔
      q = rvachevLegendrePartialSumPolynomial F N := by
  constructor
  · intro heq
    by_contra hne
    have hlt := rvachevLegendrePartialSum_strict_least_squares
      F hF N q hq hne
    linarith
  · rintro rfl
    rfl

/-- The partial sum is an `IsMinOn` minimizer on the degree-`≤ 2N + 1`
polynomial subspace. -/
theorem rvachevLegendrePartialSum_isMinOn
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    IsMinOn (rvachevLegendreSquaredError F)
      {q : ℝ[X] | q.natDegree ≤ 2 * N + 1}
      (rvachevLegendrePartialSumPolynomial F N) := by
  intro q hq
  exact rvachevLegendrePartialSum_least_squares F hF N q hq

/-- The partial sum belongs to the larger degree class on which it is
optimal.  This is stated separately because `IsMinOn` itself does not include
membership of the proposed minimizer. -/
theorem rvachevLegendrePartialSum_mem_degreeClass
    (F : BoundedFabius) (N : ℕ) :
    rvachevLegendrePartialSumPolynomial F N ∈
      {q : ℝ[X] | q.natDegree ≤ 2 * N + 1} := by
  exact (rvachevLegendrePartialSumPolynomial_natDegree_le F N).trans (by omega)

/-- Membership together with least-squares minimality on degree
`≤ 2N + 1`. -/
theorem rvachevLegendrePartialSum_mem_and_isMinOn
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    rvachevLegendrePartialSumPolynomial F N ∈
        {q : ℝ[X] | q.natDegree ≤ 2 * N + 1} ∧
      IsMinOn (rvachevLegendreSquaredError F)
        {q : ℝ[X] | q.natDegree ≤ 2 * N + 1}
        (rvachevLegendrePartialSumPolynomial F N) :=
  ⟨rvachevLegendrePartialSum_mem_degreeClass F N,
    rvachevLegendrePartialSum_isMinOn F hF N⟩

/-- In particular, the partial sum minimizes error over its visible degree
class `≤ 2N`, which is the usual meaning of “best approximation of the
corresponding degree”. -/
theorem rvachevLegendrePartialSum_isMinOn_visibleDegree
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    IsMinOn (rvachevLegendreSquaredError F)
      {q : ℝ[X] | q.natDegree ≤ 2 * N}
      (rvachevLegendrePartialSumPolynomial F N) := by
  intro q hq
  exact rvachevLegendrePartialSum_least_squares F hF N q (hq.trans (by omega))

/-- The canonical `up` partial sum is a least-squares best approximation. -/
theorem canonical_rvachevLegendrePartialSum_least_squares
    (N : ℕ) (q : ℝ[X]) (hq : q.natDegree ≤ 2 * N + 1) :
    rvachevLegendreSquaredError fabius
        (rvachevLegendrePartialSumPolynomial fabius N) ≤
      rvachevLegendreSquaredError fabius q :=
  rvachevLegendrePartialSum_least_squares fabius fabius_spec N q hq

/-- Canonical uniqueness of the best polynomial approximation. -/
theorem canonical_rvachevLegendrePartialSum_error_eq_iff
    (N : ℕ) (q : ℝ[X]) (hq : q.natDegree ≤ 2 * N + 1) :
    rvachevLegendreSquaredError fabius q =
        rvachevLegendreSquaredError fabius
          (rvachevLegendrePartialSumPolynomial fabius N) ↔
      q = rvachevLegendrePartialSumPolynomial fabius N :=
  rvachevLegendrePartialSum_error_eq_iff fabius fabius_spec N q hq

/-- Canonical `IsMinOn` form of the least-squares theorem. -/
theorem canonical_rvachevLegendrePartialSum_isMinOn (N : ℕ) :
    IsMinOn (rvachevLegendreSquaredError fabius)
      {q : ℝ[X] | q.natDegree ≤ 2 * N + 1}
      (rvachevLegendrePartialSumPolynomial fabius N) :=
  rvachevLegendrePartialSum_isMinOn fabius fabius_spec N

/-- Canonical membership and minimality package for the strongest degree
class. -/
theorem canonical_rvachevLegendrePartialSum_mem_and_isMinOn (N : ℕ) :
    rvachevLegendrePartialSumPolynomial fabius N ∈
        {q : ℝ[X] | q.natDegree ≤ 2 * N + 1} ∧
      IsMinOn (rvachevLegendreSquaredError fabius)
        {q : ℝ[X] | q.natDegree ≤ 2 * N + 1}
        (rvachevLegendrePartialSumPolynomial fabius N) :=
  rvachevLegendrePartialSum_mem_and_isMinOn fabius fabius_spec N

end

end Fabius
