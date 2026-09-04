import FabiusFunction.DyadicCombTrapezoid
import FabiusFunction.FabiusLegendreLeastSquares

/-!
# Parseval energy of the Rvachev--Legendre expansion

The even Fourier--Legendre expansion of Rvachev's `up` function already
converges absolutely and uniformly on `[-1, 1]`, and its finite partial sums
are the exact least-squares projections.  This file records the corresponding
energy identities:

* the squared norm of a finite partial sum is the finite coefficient-energy
  sum;
* the coefficient energies sum to the squared `L²[-1,1]` norm of `up`;
* the squared error of a partial sum is exactly the shifted coefficient tail;
* after reflection to `[0,1]`, the same Parseval identity gives a positive
  Legendre series for the square energy of the bounded Fabius function.

The proof of Parseval does not invoke an abstract Hilbert-basis theorem.  It
multiplies the already formalized uniformly convergent Legendre series by
`up`, commutes its absolutely dominated sum with the interval integral, and
uses the defining coefficient normalization term by term.
-/

set_option autoImplicit false

open scoped BigOperators Interval Polynomial
open Set Finset MeasureTheory Polynomial

namespace Fabius

noncomputable section

private theorem intervalIntegral_rvachevUp_mul_eval_legendrePolynomial_even
    (F : BoundedFabius) (n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      rvachevUp F x * (legendrePolynomial (2 * n)).eval x) =
      2 * rvachevLegendreCoefficient F n / (((4 * n + 1 : ℕ) : ℝ)) := by
  unfold rvachevLegendreCoefficient
  have hden : (((4 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- The `n`-th even Rvachev--Legendre block
`u_n P_(2n)`, viewed as a real-valued function. -/
noncomputable def rvachevLegendreBlock
    (F : BoundedFabius) (n : ℕ) (x : ℝ) : ℝ :=
  rvachevLegendreCoefficient F n * (legendrePolynomial (2 * n)).eval x

/-- Complete orthogonality formula for the Rvachev--Legendre blocks.  The
diagonal norm is `2 * u_n² / (4n+1)` and every off-diagonal inner product
vanishes. -/
theorem intervalIntegral_rvachevLegendreBlock_mul
    (F : BoundedFabius) (m n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      rvachevLegendreBlock F m x * rvachevLegendreBlock F n x) =
      if m = n then
        2 * (rvachevLegendreCoefficient F n) ^ 2 /
          (((4 * n + 1 : ℕ) : ℝ))
      else 0 := by
  rw [show
      (∫ x in (-1 : ℝ)..1,
        rvachevLegendreBlock F m x * rvachevLegendreBlock F n x) =
        (rvachevLegendreCoefficient F m * rvachevLegendreCoefficient F n) *
          ∫ x in (-1 : ℝ)..1,
            (legendrePolynomial (2 * m)).eval x *
              (legendrePolynomial (2 * n)).eval x by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    simp only [rvachevLegendreBlock]
    ring]
  rw [integral_eval_legendrePolynomial_mul]
  by_cases hmn : m = n
  · subst m
    simp
    ring
  · have htwone : 2 * m ≠ 2 * n := by omega
    simp [hmn, htwone]

/-- The squared norm of the `N`-th even Rvachev--Legendre partial sum is the
finite coefficient-energy sum
`sum (n ≤ N), 2 * u_n² / (4n+1)`.

This is the finite Parseval identity behind the least-squares projection. -/
theorem integral_sq_eval_rvachevLegendrePartialSumPolynomial
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      ((rvachevLegendrePartialSumPolynomial F N).eval x) ^ 2) =
      ∑ n ∈ range (N + 1),
        2 * (rvachevLegendreCoefficient F n) ^ 2 /
          (((4 * n + 1 : ℕ) : ℝ)) := by
  let S : ℝ[X] := rvachevLegendrePartialSumPolynomial F N
  have hdegree : S.natDegree ≤ 2 * N + 1 := by
    exact (rvachevLegendrePartialSumPolynomial_natDegree_le F N).trans (by omega)
  have horth := integral_rvachevUp_sub_partialSum_mul_polynomial_eq_zero
    F hF N S hdegree
  have hUpS :
      (∫ x in (-1 : ℝ)..1, rvachevUp F x * S.eval x) =
        ∑ n ∈ range (N + 1),
          2 * (rvachevLegendreCoefficient F n) ^ 2 /
            (((4 * n + 1 : ℕ) : ℝ)) := by
    rw [show
        (∫ x in (-1 : ℝ)..1, rvachevUp F x * S.eval x) =
          ∫ x in (-1 : ℝ)..1,
            ∑ n ∈ range (N + 1),
              rvachevLegendreCoefficient F n *
                (rvachevUp F x * (legendrePolynomial (2 * n)).eval x) by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [S]
      rw [eval_rvachevLegendrePartialSumPolynomial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n _hn
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral_rvachevUp_mul_eval_legendrePolynomial_even]
      ring
    · intro n _hn
      exact (continuous_const.mul
        ((rvachev_contDiff F hF).continuous.mul
          (legendrePolynomial_contDiff (2 * n)).continuous)).intervalIntegrable _ _
  have hsplit :
      (∫ x in (-1 : ℝ)..1,
        (rvachevUp F x - S.eval x) * S.eval x) =
        (∫ x in (-1 : ℝ)..1, rvachevUp F x * S.eval x) -
          ∫ x in (-1 : ℝ)..1, (S.eval x) ^ 2 := by
    rw [← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr
      intro x _hx
      ring
    · exact ((rvachev_contDiff F hF).continuous.mul S.continuous)
        |>.intervalIntegrable _ _
    · exact (S.continuous.pow 2).intervalIntegrable _ _
  change (∫ x in (-1 : ℝ)..1,
    (rvachevUp F x - S.eval x) * S.eval x) = 0 at horth
  rw [hsplit, hUpS] at horth
  linarith

/-- **Parseval for the even Rvachev--Legendre series.**  The nonnegative
coefficient energies `2 * u_n² / (4n+1)` sum to the squared unweighted
`L²[-1,1]` norm of `up`. -/
theorem hasSum_rvachevLegendreCoefficient_energy
    (F : BoundedFabius) (hF : IsFabius F) :
    HasSum (fun n : ℕ =>
      2 * (rvachevLegendreCoefficient F n) ^ 2 /
        (((4 * n + 1 : ℕ) : ℝ)))
      (∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2) := by
  let term : ℕ → C(ℝ, ℝ) := fun n =>
    ⟨fun x =>
      (rvachevLegendreCoefficient F n *
        (legendrePolynomial (2 * n)).eval x) * rvachevUp F x,
      (continuous_const.mul
        (legendrePolynomial_contDiff (2 * n)).continuous).mul
          (rvachev_contDiff F hF).continuous⟩
  let K : TopologicalSpace.Compacts ℝ :=
    ⟨uIcc (-1 : ℝ) 1, isCompact_uIcc⟩
  have htermNorm : ∀ n, ‖(term n).restrict K‖ ≤
      |rvachevLegendreCoefficient F n| := by
    intro n
    rw [ContinuousMap.norm_le _ (abs_nonneg _)]
    intro x
    have hx : (x : ℝ) ∈ Icc (-1 : ℝ) 1 := by
      have hx' := x.property
      norm_num [K, min_def, max_def] at hx'
      exact hx'
    change ‖(rvachevLegendreCoefficient F n *
      (legendrePolynomial (2 * n)).eval (x : ℝ)) * rvachevUp F (x : ℝ)‖ ≤
        |rvachevLegendreCoefficient F n|
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc
      |rvachevLegendreCoefficient F n| *
            |(legendrePolynomial (2 * n)).eval (x : ℝ)| *
                |rvachevUp F (x : ℝ)| ≤
          |rvachevLegendreCoefficient F n| * 1 * 1 := by
        gcongr
        · exact abs_eval_legendrePolynomial_le_one (2 * n) (x : ℝ) hx
        · exact abs_rvachevUp_le_one F (x : ℝ)
      _ = |rvachevLegendreCoefficient F n| := by ring
  have htermSummable : Summable fun n => ‖(term n).restrict K‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) htermNorm
      (summable_abs_rvachevLegendreCoefficient F hF)
  have hint := intervalIntegral.hasSum_intervalIntegral_of_summable_norm
    (a := (-1 : ℝ)) (b := 1) htermSummable
  have htarget :
      (∫ x in (-1 : ℝ)..1, ∑' n, term n x) =
        ∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' := hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx'
    change (∑' n,
      (rvachevLegendreCoefficient F n *
        (legendrePolynomial (2 * n)).eval x) * rvachevUp F x) =
      (rvachevUp F x) ^ 2
    simpa [pow_two] using
      ((hasSum_rvachevLegendreSeries F hF x hx').mul_right
        (rvachevUp F x)).tsum_eq
  rw [htarget] at hint
  refine HasSum.congr_fun hint ?_
  intro n
  symm
  change (∫ x in (-1 : ℝ)..1,
      (rvachevLegendreCoefficient F n *
        (legendrePolynomial (2 * n)).eval x) * rvachevUp F x) =
    2 * (rvachevLegendreCoefficient F n) ^ 2 /
      (((4 * n + 1 : ℕ) : ℝ))
  rw [show
      (∫ x in (-1 : ℝ)..1,
        (rvachevLegendreCoefficient F n *
          (legendrePolynomial (2 * n)).eval x) * rvachevUp F x) =
        rvachevLegendreCoefficient F n *
          ∫ x in (-1 : ℝ)..1,
            rvachevUp F x * (legendrePolynomial (2 * n)).eval x by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring]
  rw [intervalIntegral_rvachevUp_mul_eval_legendrePolynomial_even]
  ring

/-- The coefficient-energy tail beginning at `N+1` sums to the squared error
of the `N`-th even Legendre partial sum. -/
theorem hasSum_rvachevLegendreCoefficient_energy_tail
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    HasSum (fun n : ℕ =>
      2 * (rvachevLegendreCoefficient F (n + (N + 1))) ^ 2 /
        (((4 * (n + (N + 1)) + 1 : ℕ) : ℝ)))
      (rvachevLegendreSquaredError F
        (rvachevLegendrePartialSumPolynomial F N)) := by
  let energy : ℕ → ℝ := fun n =>
    2 * (rvachevLegendreCoefficient F n) ^ 2 /
      (((4 * n + 1 : ℕ) : ℝ))
  have hparseval : HasSum energy
      (∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2) := by
    simpa only [energy] using hasSum_rvachevLegendreCoefficient_energy F hF
  have htail := (hasSum_nat_add_iff'
    (f := energy)
    (g := ∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2)
    (N + 1)).2 hparseval
  have hpyth := rvachevLegendrePartialSum_pythagorean
    F hF N (0 : ℝ[X]) (by simp)
  have hzero : rvachevLegendreSquaredError F (0 : ℝ[X]) =
      ∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2 := by
    simp [rvachevLegendreSquaredError, legendreSquaredError]
  rw [hzero] at hpyth
  simp only [Polynomial.eval_zero, sub_zero] at hpyth
  rw [integral_sq_eval_rvachevLegendrePartialSumPolynomial F hF N] at hpyth
  have htailValue :
      (∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2) -
          ∑ n ∈ range (N + 1), energy n =
        rvachevLegendreSquaredError F
          (rvachevLegendrePartialSumPolynomial F N) := by
    simpa only [energy] using (eq_sub_of_add_eq hpyth.symm).symm
  rw [htailValue] at htail
  simpa only [energy] using htail

/-- The squared error of the `N`-th even Legendre partial sum is exactly the
coefficient-energy `tsum` tail beginning at `N+1`. -/
theorem rvachevLegendreSquaredError_partialSum_eq_tsum_tail
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) :
    rvachevLegendreSquaredError F
        (rvachevLegendrePartialSumPolynomial F N) =
      ∑' n : ℕ,
        2 * (rvachevLegendreCoefficient F (n + (N + 1))) ^ 2 /
          (((4 * (n + (N + 1)) + 1 : ℕ) : ℝ)) :=
  (hasSum_rvachevLegendreCoefficient_energy_tail F hF N).tsum_eq.symm

/-- The square energy `A₂ = integral (0..1), F(t)² dt` of a bounded Fabius
candidate. -/
noncomputable def fabiusSquareEnergy (F : BoundedFabius) : ℝ :=
  ∫ t in (0 : ℝ)..1, (fabiusReal F t) ^ 2

/-- The squared `L²[-1,1]` norm of the even `up` function is twice the square
energy of its bounded Fabius partner. -/
theorem integral_sq_rvachevUp_eq_two_mul_fabiusSquareEnergy
    (F : BoundedFabius) (hF : IsFabius F) :
    (∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2) =
      2 * fabiusSquareEnergy F := by
  have hleftInt : IntervalIntegrable
      (fun x : ℝ => (rvachevUp F x) ^ 2) volume (-1 : ℝ) 0 :=
    ((rvachev_contDiff F hF).continuous.pow 2).intervalIntegrable _ _
  have hrightInt : IntervalIntegrable
      (fun x : ℝ => (rvachevUp F x) ^ 2) volume (0 : ℝ) 1 :=
    ((rvachev_contDiff F hF).continuous.pow 2).intervalIntegrable _ _
  have hreflect := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => (rvachevUp F x) ^ 2)
    (a := (0 : ℝ)) (b := 1)
  have hleft :
      (∫ x in (-1 : ℝ)..0, (rvachevUp F x) ^ 2) =
        ∫ x in (0 : ℝ)..1, (rvachevUp F x) ^ 2 := by
    symm
    calc
      (∫ x in (0 : ℝ)..1, (rvachevUp F x) ^ 2) =
          ∫ x in (0 : ℝ)..1, (rvachevUp F (-x)) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _hx
        change (rvachevUp F x) ^ 2 = (rvachevUp F (-x)) ^ 2
        rw [rvachevUp_even F]
      _ = ∫ x in (-1 : ℝ)..0, (rvachevUp F x) ^ 2 := by
        simpa using hreflect
  have hhalf :
      (∫ x in (0 : ℝ)..1, (rvachevUp F x) ^ 2) =
        fabiusSquareEnergy F := by
    rw [fabiusSquareEnergy]
    calc
      (∫ x in (0 : ℝ)..1, (rvachevUp F x) ^ 2) =
          ∫ x in (0 : ℝ)..1, (fabiusReal F (1 - x)) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' := hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx'
        change (rvachevUp F x) ^ 2 = (fabiusReal F (1 - x)) ^ 2
        rw [rvachevUp_eq_fabiusReal_one_sub F hx'.1]
      _ = ∫ t in (0 : ℝ)..1, (fabiusReal F t) ^ 2 :=
        intervalIntegral_comp_one_sub_unit fun t => (fabiusReal F t) ^ 2
  calc
    (∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2) =
        (∫ x in (-1 : ℝ)..0, (rvachevUp F x) ^ 2) +
          ∫ x in (0 : ℝ)..1, (rvachevUp F x) ^ 2 := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt
    _ = 2 * fabiusSquareEnergy F := by rw [hleft, hhalf]; ring

/-- The positive Legendre coefficient series sums to the Fabius square
energy `A₂`; this is the real-variable Legendre part of the report's
three-way energy identity. -/
theorem hasSum_fabiusSquareEnergy_legendre
    (F : BoundedFabius) (hF : IsFabius F) :
    HasSum (fun n : ℕ =>
      (rvachevLegendreCoefficient F n) ^ 2 /
        (((4 * n + 1 : ℕ) : ℝ)))
      (fabiusSquareEnergy F) := by
  have h := (hasSum_rvachevLegendreCoefficient_energy F hF).mul_left (1 / 2 : ℝ)
  have hseq : HasSum (fun n : ℕ =>
      (rvachevLegendreCoefficient F n) ^ 2 /
        (((4 * n + 1 : ℕ) : ℝ)))
      ((1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2) := by
    refine HasSum.congr_fun h ?_
    intro n
    ring
  have hsum :
      (1 / 2 : ℝ) * (∫ x in (-1 : ℝ)..1, (rvachevUp F x) ^ 2) =
        fabiusSquareEnergy F := by
    rw [integral_sq_rvachevUp_eq_two_mul_fabiusSquareEnergy F hF]
    ring
  rw [hsum] at hseq
  exact hseq

/-- `tsum` form of the positive Legendre series for the Fabius square
energy. -/
theorem fabiusSquareEnergy_eq_tsum_legendre
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusSquareEnergy F =
      ∑' n : ℕ,
        (rvachevLegendreCoefficient F n) ^ 2 /
          (((4 * n + 1 : ℕ) : ℝ)) :=
  (hasSum_fabiusSquareEnergy_legendre F hF).tsum_eq.symm

end

end Fabius
