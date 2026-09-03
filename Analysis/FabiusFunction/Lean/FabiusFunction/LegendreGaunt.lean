import FabiusFunction.FabiusLegendreLeastSquares
import FabiusFunction.FiniteMomentGram
import FabiusFunction.LegendrePolynomialRational
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Executable rational Legendre Gaunt coefficients

This module gives a finite rational realization of the triple products of
ordinary Legendre polynomials.  The Lebesgue moments of `[-1, 1]` and the
coefficient arrays of the three polynomials produce an executable bounded
triple sum.  Casting that sum to `ℝ` recovers the corresponding interval
integral, and the finite Fourier--Legendre projection gives exact product
linearization over both `ℝ` and `ℚ`.

The construction is total at every triple of natural-number indices.  Its
parity and triangle-support zeros are proved consequences, rather than
conditions built into the definition.  No Wigner `3j` formula, factorial
closed form, positivity theorem, or asymptotic claim is made here.
-/

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators Interval Polynomial

namespace Fabius

/-! ## Executable rational data -/

/-- The executable `n`-th monomial moment of Lebesgue measure on `[-1,1]`.
It is `2 / (n + 1)` for even `n` and zero for odd `n`. -/
def legendreLebesgueMomentRat (n : ℕ) : ℚ :=
  if n % 2 = 0 then 2 / (((n + 1 : ℕ) : ℚ)) else 0

/-- The executable rational Gaunt coefficient, written as the bounded triple
coefficient sum for `P_i P_j P_k` against the Lebesgue moments of `[-1,1]`.
The definition is total; parity and triangle-support zeros are established
below. -/
def legendreGauntRat (i j k : ℕ) : ℚ :=
  ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1), ∑ c ∈ range (k + 1),
    legendrePolynomialCoeffRat i a *
      legendrePolynomialCoeffRat j b *
        legendrePolynomialCoeffRat k c *
          legendreLebesgueMomentRat (a + b + c)

/-- The real Gaunt integral of three ordinary Legendre polynomials on their
natural interval `[-1,1]`. -/
noncomputable def legendreGaunt (i j k : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    (legendrePolynomial i).eval x *
      (legendrePolynomial j).eval x *
        (legendrePolynomial k).eval x

/-- The executable rational coefficient of `P_k` in the finite product
linearization of `P_i P_j`.  The normalization is the ordinary Legendre
factor `(2k+1)/2`; outside the parity and triangle support it evaluates to
zero by the theorems below. -/
def legendreProductLinearizationCoeffRat (i j k : ℕ) : ℚ :=
  (((2 * k + 1 : ℕ) : ℚ) / 2) * legendreGauntRat i j k

noncomputable section

/-! ## Moment and integral bridges -/

/-- The executable Lebesgue moment at an even index. -/
theorem legendreLebesgueMomentRat_even (n : ℕ) :
    legendreLebesgueMomentRat (2 * n) =
      2 / (((2 * n + 1 : ℕ) : ℚ)) := by
  rw [legendreLebesgueMomentRat, if_pos (by omega)]

/-- The executable Lebesgue moment at an odd index vanishes. -/
theorem legendreLebesgueMomentRat_odd (n : ℕ) :
    legendreLebesgueMomentRat (2 * n + 1) = 0 := by
  rw [legendreLebesgueMomentRat, if_neg (by omega)]

/-- Casting an executable Lebesgue moment to `ℝ` gives the corresponding
monomial interval integral on `[-1,1]`. -/
theorem legendreLebesgueMomentRat_cast (n : ℕ) :
    (legendreLebesgueMomentRat n : ℝ) =
      ∫ x in (-1 : ℝ)..1, x ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [legendreLebesgueMomentRat_even, integral_pow]
    norm_num [pow_succ, pow_mul]
  · rw [legendreLebesgueMomentRat_odd, integral_pow]
    norm_num [pow_succ, pow_mul]

private theorem momentFunctional_legendreLebesgueMomentRat_cast
    (p : ℚ[X]) :
    (momentFunctional legendreLebesgueMomentRat p : ℝ) =
      ∫ x in (-1 : ℝ)..1, (p.map (Rat.castHom ℝ)).eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      calc
        (momentFunctional legendreLebesgueMomentRat (p + q) : ℝ) =
            (momentFunctional legendreLebesgueMomentRat p : ℝ) +
              (momentFunctional legendreLebesgueMomentRat q : ℝ) := by
                simp only [map_add, Rat.cast_add]
        _ = (∫ x in (-1 : ℝ)..1,
              (p.map (Rat.castHom ℝ)).eval x) +
            ∫ x in (-1 : ℝ)..1,
              (q.map (Rat.castHom ℝ)).eval x := by rw [hp, hq]
        _ = ∫ x in (-1 : ℝ)..1,
              (p.map (Rat.castHom ℝ)).eval x +
                (q.map (Rat.castHom ℝ)).eval x := by
            have hpInt : IntervalIntegrable
                (fun x : ℝ ↦ (p.map (Rat.castHom ℝ)).eval x)
                MeasureTheory.volume (-1) 1 :=
              (p.map (Rat.castHom ℝ)).continuous.intervalIntegrable _ _
            have hqInt : IntervalIntegrable
                (fun x : ℝ ↦ (q.map (Rat.castHom ℝ)).eval x)
                MeasureTheory.volume (-1) 1 :=
              (q.map (Rat.castHom ℝ)).continuous.intervalIntegrable _ _
            symm
            exact intervalIntegral.integral_add hpInt hqInt
        _ = ∫ x in (-1 : ℝ)..1,
              ((p + q).map (Rat.castHom ℝ)).eval x := by
            apply intervalIntegral.integral_congr
            intro x _hx
            simp
  | monomial n a =>
      calc
        (momentFunctional legendreLebesgueMomentRat
            (Polynomial.monomial n a) : ℝ) =
            (a : ℝ) * (legendreLebesgueMomentRat n : ℝ) := by
              simp only [momentFunctional_monomial, Rat.cast_mul]
        _ = (a : ℝ) * (∫ x in (-1 : ℝ)..1, x ^ n) := by
              rw [legendreLebesgueMomentRat_cast]
        _ = ∫ x in (-1 : ℝ)..1, (a : ℝ) * x ^ n := by
              rw [intervalIntegral.integral_const_mul]
        _ = ∫ x in (-1 : ℝ)..1,
              ((Polynomial.monomial n a).map (Rat.castHom ℝ)).eval x := by
            apply intervalIntegral.integral_congr
            intro x _hx
            simp [mul_comm]

private theorem sum_comm_three
    {A B C M : Type*} [AddCommMonoid M]
    (s : Finset A) (t : Finset B) (u : Finset C)
    (f : A → B → C → M) :
    (∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c) =
      ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c := by
  calc
    (∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c) =
        ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.sum_comm]
    _ = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]

/-- The executable triple sum is the rational moment functional applied to
the product of the three rational Legendre polynomials. -/
theorem legendreGauntRat_eq_momentFunctional (i j k : ℕ) :
    legendreGauntRat i j k =
      momentFunctional legendreLebesgueMomentRat
        (legendrePolynomialRat i * legendrePolynomialRat j *
          legendrePolynomialRat k) := by
  have hi : (legendrePolynomialRat i).natDegree < i + 1 := by simp
  have hj : (legendrePolynomialRat j).natDegree < j + 1 := by simp
  have hk : (legendrePolynomialRat k).natDegree < k + 1 := by simp
  have hiExpansion :=
    (legendrePolynomialRat i).as_sum_range_C_mul_X_pow' hi
  have hjExpansion :=
    (legendrePolynomialRat j).as_sum_range_C_mul_X_pow' hj
  have hkExpansion :=
    (legendrePolynomialRat k).as_sum_range_C_mul_X_pow' hk
  calc
    legendreGauntRat i j k =
        ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
          ∑ c ∈ range (k + 1),
            legendrePolynomialCoeffRat i a *
              legendrePolynomialCoeffRat j b *
                legendrePolynomialCoeffRat k c *
                  legendreLebesgueMomentRat (a + b + c) := rfl
    _ = momentFunctional legendreLebesgueMomentRat
        ((∑ a ∈ range (i + 1),
            C ((legendrePolynomialRat i).coeff a) * X ^ a) *
          (∑ b ∈ range (j + 1),
            C ((legendrePolynomialRat j).coeff b) * X ^ b) *
          (∑ c ∈ range (k + 1),
            C ((legendrePolynomialRat k).coeff c) * X ^ c)) := by
      symm
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum,
        Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.monomial_mul_monomial, momentFunctional_monomial,
        coeff_legendrePolynomialRat, add_assoc]
      rw [sum_comm_three]
    _ = momentFunctional legendreLebesgueMomentRat
        (legendrePolynomialRat i * legendrePolynomialRat j *
          legendrePolynomialRat k) := by
      rw [← hiExpansion, ← hjExpansion, ← hkExpansion]

/-- Casting the executable rational triple sum to `ℝ` recovers the real
Gaunt interval integral. -/
theorem legendreGauntRat_cast (i j k : ℕ) :
    (legendreGauntRat i j k : ℝ) = legendreGaunt i j k := by
  rw [legendreGauntRat_eq_momentFunctional]
  simpa only [Polynomial.map_mul, legendrePolynomialRat_cast,
    Polynomial.eval_mul, legendreGaunt] using
      momentFunctional_legendreLebesgueMomentRat_cast
        (legendrePolynomialRat i * legendrePolynomialRat j *
          legendrePolynomialRat k)

/-! ## Symmetry and finite product linearization -/

/-- Swapping the first two indices leaves the rational Gaunt coefficient
unchanged. -/
theorem legendreGauntRat_swap_left (i j k : ℕ) :
    legendreGauntRat i j k = legendreGauntRat j i k := by
  rw [legendreGauntRat_eq_momentFunctional,
    legendreGauntRat_eq_momentFunctional]
  congr 1
  ring

/-- Swapping the final two indices leaves the rational Gaunt coefficient
unchanged. -/
theorem legendreGauntRat_swap_right (i j k : ℕ) :
    legendreGauntRat i j k = legendreGauntRat i k j := by
  rw [legendreGauntRat_eq_momentFunctional,
    legendreGauntRat_eq_momentFunctional]
  congr 1
  ring

private theorem legendreProductLinearizationCoeffRat_cast
    (i j k : ℕ) :
    (legendreProductLinearizationCoeffRat i j k : ℝ) =
      (((2 * k + 1 : ℕ) : ℝ) / 2) * legendreGaunt i j k := by
  norm_num [legendreProductLinearizationCoeffRat, legendreGauntRat_cast]

/-- The product of two real Legendre polynomials is the finite Legendre sum
whose coefficients are the casts of the executable rational Gaunt
coefficients. -/
theorem legendrePolynomial_mul_eq_sum_gaunt (i j : ℕ) :
    legendrePolynomial i * legendrePolynomial j =
      ∑ k ∈ range (i + j + 1),
        (legendreProductLinearizationCoeffRat i j k : ℝ) •
          legendrePolynomial k := by
  have hdegree :
      (legendrePolynomial i * legendrePolynomial j).degree ≤ i + j := by
    calc
      (legendrePolynomial i * legendrePolynomial j).degree ≤
          (legendrePolynomial i).degree +
            (legendrePolynomial j).degree :=
        Polynomial.degree_mul_le _ _
      _ = i + j := by simp
  calc
    legendrePolynomial i * legendrePolynomial j =
        legendreProjectionPolynomial
          (fun x : ℝ ↦
            (legendrePolynomial i * legendrePolynomial j).eval x)
          (i + j) :=
      (legendreProjectionPolynomial_eval_eq_self (i + j)
        (legendrePolynomial i * legendrePolynomial j) hdegree).symm
    _ = ∑ k ∈ range (i + j + 1),
        (legendreProductLinearizationCoeffRat i j k : ℝ) •
          legendrePolynomial k := by
      rw [legendreProjectionPolynomial]
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [legendreSeriesCoefficientOf, Polynomial.eval_mul,
        legendreProductLinearizationCoeffRat_cast, legendreGaunt]

/-- The same finite product linearization holds exactly over `ℚ`; hence
the complete coefficient array is executable without evaluating a real
integral.  Its proof reflects the real integral identity through the
injective coefficientwise cast. -/
theorem legendrePolynomialRat_mul_eq_sum_gaunt (i j : ℕ) :
    legendrePolynomialRat i * legendrePolynomialRat j =
      ∑ k ∈ range (i + j + 1),
        legendreProductLinearizationCoeffRat i j k •
          legendrePolynomialRat k := by
  apply Polynomial.map_injective (f := Rat.castHom ℝ)
    (Rat.cast_injective (α := ℝ))
  simp only [Polynomial.map_mul, legendrePolynomialRat_cast,
    Polynomial.map_sum, Polynomial.map_smul]
  change legendrePolynomial i * legendrePolynomial j =
    ∑ k ∈ range (i + j + 1),
      (legendreProductLinearizationCoeffRat i j k : ℝ) •
        legendrePolynomial k
  exact legendrePolynomial_mul_eq_sum_gaunt i j

/-! ## Parity and triangle support -/

/-- A Gaunt coefficient vanishes when the sum of its three indices is odd. -/
theorem legendreGauntRat_eq_zero_of_odd_sum
    {i j k : ℕ} (hodd : Odd (i + j + k)) :
    legendreGauntRat i j k = 0 := by
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_zero, legendreGauntRat_cast]
  let g : ℝ → ℝ := fun x ↦
    (legendrePolynomial i).eval x *
      (legendrePolynomial j).eval x *
        (legendrePolynomial k).eval x
  have hsign :
      (-1 : ℝ) ^ i * (-1 : ℝ) ^ j * (-1 : ℝ) ^ k = -1 := by
    rw [← pow_add, ← pow_add]
    exact Odd.neg_one_pow hodd
  have hgOdd (x : ℝ) : g (-x) = -g x := by
    dsimp [g]
    rw [eval_legendrePolynomial_neg, eval_legendrePolynomial_neg,
      eval_legendrePolynomial_neg]
    calc
      ((-1 : ℝ) ^ i * (legendrePolynomial i).eval x) *
            ((-1 : ℝ) ^ j * (legendrePolynomial j).eval x) *
          ((-1 : ℝ) ^ k * (legendrePolynomial k).eval x) =
          ((-1 : ℝ) ^ i * (-1 : ℝ) ^ j * (-1 : ℝ) ^ k) *
            ((legendrePolynomial i).eval x *
              (legendrePolynomial j).eval x *
                (legendrePolynomial k).eval x) := by ring
      _ = -(g x) := by rw [hsign]; simp [g]
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
  change (∫ x in (-1 : ℝ)..1, g x) = 0
  linarith

private theorem legendreGaunt_eq_zero_of_add_lt
    {i j k : ℕ} (hijk : i + j < k) :
    legendreGaunt i j k = 0 := by
  calc
    legendreGaunt i j k =
        ∫ x in (-1 : ℝ)..1,
          (legendrePolynomial i * legendrePolynomial j).eval x *
            (legendrePolynomial k).eval x := by
      simp only [legendreGaunt, Polynomial.eval_mul]
    _ = ∫ x in (-1 : ℝ)..1,
          (∑ l ∈ range (i + j + 1),
            (legendreProductLinearizationCoeffRat i j l : ℝ) •
              legendrePolynomial l).eval x *
            (legendrePolynomial k).eval x := by
      rw [legendrePolynomial_mul_eq_sum_gaunt]
    _ = ∑ l ∈ range (i + j + 1),
          (legendreProductLinearizationCoeffRat i j l : ℝ) *
            (∫ x in (-1 : ℝ)..1,
              (legendrePolynomial l).eval x *
                (legendrePolynomial k).eval x) := by
      rw [show
          (∫ x in (-1 : ℝ)..1,
            (∑ l ∈ range (i + j + 1),
              (legendreProductLinearizationCoeffRat i j l : ℝ) •
                legendrePolynomial l).eval x *
              (legendrePolynomial k).eval x) =
            ∫ x in (-1 : ℝ)..1,
              ∑ l ∈ range (i + j + 1),
                (legendreProductLinearizationCoeffRat i j l : ℝ) *
                  ((legendrePolynomial l).eval x *
                    (legendrePolynomial k).eval x) by
        apply intervalIntegral.integral_congr
        intro x _hx
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul,
          smul_eq_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _hl
        ring]
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro l _hl
        rw [intervalIntegral.integral_const_mul]
      · intro l _hl
        apply Continuous.intervalIntegrable
        fun_prop
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      have hlk : l < k := by
        have hlrange : l < i + j + 1 := Finset.mem_range.mp hl
        omega
      rw [integral_eval_legendrePolynomial_mul_eq_zero_of_ne
        (Nat.ne_of_lt hlk), mul_zero]

/-- The rational Gaunt coefficient vanishes above the degree of the product:
if `i + j < k`, then the `P_k` component of `P_i P_j` is zero. -/
theorem legendreGauntRat_eq_zero_of_add_lt
    {i j k : ℕ} (hijk : i + j < k) :
    legendreGauntRat i j k = 0 := by
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_zero, legendreGauntRat_cast] using
    legendreGaunt_eq_zero_of_add_lt hijk

/-- The rational Gaunt coefficient vanishes whenever any strict triangle
inequality fails.  Together with the odd-sum theorem, these are the necessary
support restrictions proved here; no converse or closed Wigner-symbol formula
is asserted. -/
theorem legendreGauntRat_eq_zero_of_triangle_violation
    {i j k : ℕ}
    (htriangle : i + j < k ∨ i + k < j ∨ j + k < i) :
    legendreGauntRat i j k = 0 := by
  rcases htriangle with hijk | hikj | hjki
  · exact legendreGauntRat_eq_zero_of_add_lt hijk
  · calc
      legendreGauntRat i j k = legendreGauntRat i k j :=
        legendreGauntRat_swap_right i j k
      _ = 0 := legendreGauntRat_eq_zero_of_add_lt hikj
  · calc
      legendreGauntRat i j k = legendreGauntRat j i k :=
        legendreGauntRat_swap_left i j k
      _ = legendreGauntRat j k i := legendreGauntRat_swap_right j i k
      _ = 0 := legendreGauntRat_eq_zero_of_add_lt hjki

end

end Fabius
