import Mathlib.Analysis.Real.Sqrt
import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def exchangeTransfer {J K : Type*} (a : J → ℂ) (b : K → ℂ)
    (i : J) (j : K) (k : J) (l : K) : ℂ :=
  (a i * star (a k)) * (b l * star (b j))

theorem exchange_transfer_diagonal {J K : Type*} (a : J → ℂ) (b : K → ℂ) (i : J) (j : K) :
    exchangeTransfer a b i j i j = (‖star (a i) * b j‖ ^ 2 : ℝ) := by
  simp only [norm_mul, norm_star, mul_pow, Complex.ofReal_mul]
  simp only [exchangeTransfer, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem exchange_transfer_identity {J K : Type*} (a : J → ℂ) (b : K → ℂ)
    (i k : J) (j l : K) :
    (star (a i) * b j) * exchangeTransfer a b i j k l =
      (‖star (a i) * b j‖ ^ 2 : ℝ) * (star (a k) * b l) := by
  rw [← exchange_transfer_diagonal a b i j]
  unfold exchangeTransfer
  ring

theorem exchange_error_identity {J K : Type*} (a : J → ℂ) (b : K → ℂ)
    (i k : J) (j l : K) (w : ℝ) (g : ℂ) :
    (star (a k) * b l) * (w * ‖star (a i) * b j‖ ^ 2 : ℝ) -
        g * exchangeTransfer a b i j k l =
      ((star (a i) * b j) * (w : ℂ) - g) * exchangeTransfer a b i j k l := by
  rw [Complex.ofReal_mul]
  calc
    _ = (w : ℂ) * ((‖star (a i) * b j‖ ^ 2 : ℝ) * (star (a k) * b l)) -
        g * exchangeTransfer a b i j k l := by ring
    _ = (w : ℂ) * ((star (a i) * b j) * exchangeTransfer a b i j k l) -
        g * exchangeTransfer a b i j k l := by rw [exchange_transfer_identity]
    _ = _ := by ring

theorem exchange_transfer_square_sum {J K : Type*} [Fintype J] [Fintype K]
    (a : J → ℂ) (b : K → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1) (hb : ∑ l, ‖b l‖ ^ 2 = 1)
    (i : J) (j : K) :
    (∑ k, ∑ l, ‖exchangeTransfer a b i j k l‖ ^ 2) = ‖a i‖ ^ 2 * ‖b j‖ ^ 2 := by
  calc
    _ = (∑ k, ‖a k‖ ^ 2) * (∑ l, ‖b l‖ ^ 2) * (‖a i‖ ^ 2 * ‖b j‖ ^ 2) := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      simp only [exchangeTransfer, norm_mul, norm_star, mul_pow]
      ring
    _ = _ := by rw [ha, hb]; ring

theorem exchange_matrix_error_le {J K : Type*} [Fintype J] [Fintype K]
    (a : J → ℂ) (b : K → ℂ) (ha : ∑ k, ‖a k‖ ^ 2 = 1) (hb : ∑ l, ‖b l‖ ^ 2 = 1)
    (i : J) (j : K) (hi : ‖a i‖ ≤ 1) (hj : ‖b j‖ ≤ 1) (w : ℝ) (g : ℂ) :
    Real.sqrt (∑ k, ∑ l,
      ‖(star (a k) * b l) * (w * ‖star (a i) * b j‖ ^ 2 : ℝ) -
        g * exchangeTransfer a b i j k l‖ ^ 2) ≤ ‖(star (a i) * b j) * (w : ℂ) - g‖ := by
  let e := (star (a i) * b j) * (w : ℂ) - g
  have hsq : (∑ k, ∑ l,
      ‖(star (a k) * b l) * (w * ‖star (a i) * b j‖ ^ 2 : ℝ) -
        g * exchangeTransfer a b i j k l‖ ^ 2) =
      ‖e‖ ^ 2 * (‖a i‖ ^ 2 * ‖b j‖ ^ 2) := by
    simp_rw [exchange_error_identity, norm_mul, mul_pow]
    calc
      _ = ‖e‖ ^ 2 * (∑ k, ∑ l, ‖exchangeTransfer a b i j k l‖ ^ 2) := by
        simp only [Finset.mul_sum, e]
      _ = _ := by rw [exchange_transfer_square_sum a b ha hb i j]
  have hcoeff : ‖a i‖ ^ 2 * ‖b j‖ ^ 2 ≤ 1 := by
    have hi2 : ‖a i‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (a i)]
    have hj2 : ‖b j‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (b j)]
    exact (mul_le_of_le_one_left (sq_nonneg _) hi2).trans hj2
  apply (Real.sqrt_le_sqrt (show _ ≤ ‖e‖ ^ 2 from ?_)).trans (Real.sqrt_sq (norm_nonneg e)).le
  rw [hsq]
  exact mul_le_of_le_one_right (sq_nonneg _) hcoeff

end Erdos3

end

end OAI
