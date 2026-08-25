import FabiusFunction.LegendrePolynomial
import FabiusFunction.Paper06487Supplement

/-!
# Legendre coefficients of Rvachev's up function

This module evaluates the Fourier--Legendre coefficient of the even function
`rvachevUp F` in terms of the inverse-power-of-two values of the associated
bounded Fabius function.  The coefficient is normalized for the ordinary
Legendre basis on `[-1, 1]`:

`u_n = (4n + 1) / 2 * ∫_(-1)^1 up(x) P_(2n)(x) dx`.
-/

set_option autoImplicit false

open scoped BigOperators Interval
open Set Finset MeasureTheory Polynomial

namespace Fabius

noncomputable section

/-- The coefficient of `P_(2n)` in the Fourier--Legendre expansion of
Rvachev's `up` function. -/
noncomputable def rvachevLegendreCoefficient
    (F : BoundedFabius) (n : ℕ) : ℝ :=
  ((4 * n + 1 : ℕ) : ℝ) / 2 *
    ∫ x in (-1 : ℝ)..1,
      rvachevUp F x * (legendrePolynomial (2 * n)).eval x

/-- The coefficient of `P_j` in the full Fourier--Legendre expansion.  The
even subsequence is `rvachevLegendreCoefficient`. -/
noncomputable def rvachevFullLegendreCoefficient
    (F : BoundedFabius) (j : ℕ) : ℝ :=
  ((2 * j + 1 : ℕ) : ℝ) / 2 *
    ∫ x in (-1 : ℝ)..1,
      rvachevUp F x * (legendrePolynomial j).eval x

/-- The even-indexed full coefficient is the coefficient used in the
displayed expansion. -/
theorem rvachevFullLegendreCoefficient_even_eq
    (F : BoundedFabius) (n : ℕ) :
    rvachevFullLegendreCoefficient F (2 * n) =
      rvachevLegendreCoefficient F n := by
  unfold rvachevFullLegendreCoefficient rvachevLegendreCoefficient
  congr 1
  push_cast
  ring

/-- All odd Fourier--Legendre coefficients of Rvachev's even function
vanish. -/
theorem rvachevFullLegendreCoefficient_odd_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    rvachevFullLegendreCoefficient F (2 * n + 1) = 0 := by
  let g : ℝ → ℝ := fun x =>
    rvachevUp F x * (legendrePolynomial (2 * n + 1)).eval x
  have hgOdd (x : ℝ) : g (-x) = -g x := by
    dsimp [g]
    rw [rvachev_even F hF, eval_legendrePolynomial_neg]
    rw [pow_add, pow_mul]
    norm_num
  have hreflect := intervalIntegral.integral_comp_neg
    (f := g) (a := (-1 : ℝ)) (b := 1)
  have hsymmetric :
      (∫ x in (-1 : ℝ)..1, g (-x)) =
        ∫ x in (-1 : ℝ)..1, g x := by
    simpa only [neg_neg] using hreflect
  have hnegative :
      (∫ x in (-1 : ℝ)..1, g (-x)) =
        -∫ x in (-1 : ℝ)..1, g x := by
    calc
      (∫ x in (-1 : ℝ)..1, g (-x)) =
          ∫ x in (-1 : ℝ)..1, -g x := by
            apply intervalIntegral.integral_congr
            intro x _hx
            exact hgOdd x
      _ = -∫ x in (-1 : ℝ)..1, g x :=
        intervalIntegral.integral_neg
  have hzero : (∫ x in (-1 : ℝ)..1, g x) = 0 := by
    linarith
  rw [rvachevFullLegendreCoefficient]
  change ((2 * (2 * n + 1) + 1 : ℕ) : ℝ) / 2 *
      (∫ x in (-1 : ℝ)..1, g x) = 0
  rw [hzero, mul_zero]

/-- The even power moments over the support interval are the exact arithmetic
moments `moment k`. -/
theorem integral_even_power_mul_rvachev_eq_moment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    (∫ x in (-1 : ℝ)..1, x ^ (2 * k) * rvachevUp F x) =
      (moment k : ℝ) := by
  have hsupport :
      Function.support (fun x : ℝ => x ^ (2 * k) * rvachevUp F x) ⊆
        Ioc (-1 : ℝ) 1 := by
    intro x hx
    have hup : rvachevUp F x ≠ 0 := by
      intro hz
      apply hx
      simp [hz]
    have hmem := support_rvachev_subset F hF hup
    have hxne : x ≠ -1 := by
      intro heq
      subst x
      exact hup (rvachevUp_eq_zero_of_le_neg_one F hF le_rfl)
    exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hxne), hmem.2⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupport]
  exact (moment_eq_integral F hF k).symm

/-- Express the `2k`-th moment of `up` as a reciprocal-power-of-two value of
the bounded Fabius function. -/
theorem moment_eq_two_mul_fabius_dyadic
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    (moment k : ℝ) =
      2 * (Nat.factorial (2 * k) : ℝ) *
        2 ^ (2 * k + 1).choose 2 *
        fabiusReal F (((2 : ℝ) ^ (2 * k + 1))⁻¹) := by
  have h := moment_halfIntegral_eq_rvachev_dyadic F hF k
  have hhalf :
      (moment k : ℝ) / 2 =
        (Nat.factorial (2 * k) : ℝ) *
          2 ^ (2 * k + 1).choose 2 *
          rvachevUp F (1 - ((2 : ℝ) ^ (2 * k + 1))⁻¹) :=
    h.1.trans h.2
  rw [rvachev_one_sub_inverse_two_pow_eq_fabius F hF (2 * k + 1)] at hhalf
  linarith

/-- The exact finite formula for the `P_(2n)` coefficient of Rvachev's
`up` function. -/
theorem rvachevLegendreCoefficient_eq_fabius_sum
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    rvachevLegendreCoefficient F n =
      (4 : ℝ)⁻¹ ^ n * ((4 * n + 1 : ℕ) : ℝ) *
        ∑ k ∈ range (n + 1),
          (-1 : ℝ) ^ (n + k) *
            (2 * n).choose (n + k) *
            (2 * n + 2 * k).choose (2 * n) *
            (Nat.factorial (2 * k) : ℝ) *
            2 ^ (2 * k + 1).choose 2 *
            fabiusReal F (((2 : ℝ) ^ (2 * k + 1))⁻¹) := by
  have hint :
      (∫ x in (-1 : ℝ)..1,
          rvachevUp F x * (legendrePolynomial (2 * n)).eval x) =
        ∑ k ∈ range (n + 1),
          ((4 : ℝ)⁻¹ ^ n *
            ((-1 : ℝ) ^ (n + k) *
              (2 * n).choose (n + k) *
              (2 * n + 2 * k).choose (2 * n))) *
            (∫ x in (-1 : ℝ)..1,
              x ^ (2 * k) * rvachevUp F x) := by
    rw [show
        (∫ x in (-1 : ℝ)..1,
          rvachevUp F x * (legendrePolynomial (2 * n)).eval x) =
          ∫ x in (-1 : ℝ)..1,
            ∑ k ∈ range (n + 1),
              ((4 : ℝ)⁻¹ ^ n *
                ((-1 : ℝ) ^ (n + k) *
                  (2 * n).choose (n + k) *
                  (2 * n + 2 * k).choose (2 * n))) *
                (x ^ (2 * k) * rvachevUp F x) by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only
      rw [eval_legendrePolynomial_even]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul]
    · intro k hk
      exact
        (continuous_const.mul
          ((continuous_id.pow (2 * k)).mul
            (rvachev_contDiff F hF).continuous)).intervalIntegrable (-1) 1
  rw [rvachevLegendreCoefficient, hint]
  simp_rw [integral_even_power_mul_rvachev_eq_moment F hF,
    moment_eq_two_mul_fabius_dyadic F hF]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Canonical specialization of `rvachevLegendreCoefficient_eq_fabius_sum`.
This is the coefficient formula in the displayed claim. -/
theorem canonical_rvachevLegendreCoefficient_eq_fabius_sum (n : ℕ) :
    rvachevLegendreCoefficient fabius n =
      (4 : ℝ)⁻¹ ^ n * ((4 * n + 1 : ℕ) : ℝ) *
        ∑ k ∈ range (n + 1),
          (-1 : ℝ) ^ (n + k) *
            (2 * n).choose (n + k) *
            (2 * n + 2 * k).choose (2 * n) *
            (Nat.factorial (2 * k) : ℝ) *
            2 ^ (2 * k + 1).choose 2 *
            fabiusReal fabius (((2 : ℝ) ^ (2 * k + 1))⁻¹) := by
  exact rvachevLegendreCoefficient_eq_fabius_sum fabius fabius_spec n

end

end Fabius
