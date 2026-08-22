import Mathlib

/-!
# Positive-coefficient rank-one closure

This file isolates the finite covariance identity behind a post-report sufficient condition.
If a power-series interpolant has nonnegative coefficients of total mass one, then the
rank-one identity at `1, 2, 3, 6` forces all mass onto a single exponent.  The passage from
finite coefficient vectors to an entire nonnegative series is a paper-level Tonelli argument.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace PositiveCoefficientClosure

open scoped BigOperators

theorem two_mul_covariance_identity
    {ι : Type*} [Fintype ι]
    (w f g : ι → ℝ) :
    2 * ((∑ i, w i) * (∑ i, w i * f i * g i)
        - (∑ i, w i * f i) * (∑ i, w i * g i)) =
      ∑ i, ∑ j, w i * w j * (f i - f j) * (g i - g j) := by
  classical
  have swap (h : ι → ι → ℝ) :
      (∑ i, ∑ j, h i j) = ∑ i, ∑ j, h j i := by
    rw [Finset.sum_comm]
  have hcross :
      (∑ i, ∑ j, w i * w j * f j * g i) =
        ∑ i, ∑ j, w i * w j * f i * g j := by
    calc
      _ = ∑ i, ∑ j, w j * w i * f i * g j :=
        swap (fun i j => w i * w j * f j * g i)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hdiag :
      (∑ i, ∑ j, w i * w j * f j * g j) =
        ∑ i, ∑ j, w i * w j * f i * g i := by
    calc
      _ = ∑ i, ∑ j, w j * w i * f i * g i :=
        swap (fun i j => w i * w j * f j * g j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp only [mul_assoc, mul_left_comm, mul_comm]
  have hcross' :
      (∑ i, ∑ j, w i * (w j * (f j * g i))) =
        ∑ i, ∑ j, w i * (w j * (f i * g j)) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcross
  have hdiag' :
      (∑ i, ∑ j, w i * (w j * (f j * g j))) =
        ∑ i, ∑ j, w i * (w j * (f i * g i)) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hdiag
  rw [← hcross', hdiag']
  have hdiag_two :
      (∑ i, ∑ j, w i * (w j * (f i * (g i * 2)))) =
        (∑ i, ∑ j, w i * (w j * (f i * g i))) * 2 := by
    calc
      _ = ∑ i, ∑ j, (w i * (w j * (f i * g i))) * 2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by simp only [Finset.sum_mul]
  have hcross_two :
      (∑ i, ∑ j, w i * (w j * (f j * (g i * 2)))) =
        (∑ i, ∑ j, w i * (w j * (f j * g i))) * 2 := by
    calc
      _ = ∑ i, ∑ j, (w i * (w j * (f j * g i))) * 2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by simp only [Finset.sum_mul]
  rw [hdiag_two, hcross_two]
  ring

/-- The pair kernel for the two bases is nonnegative. -/
theorem pow_two_three_pair_nonneg (i j : ℕ) :
    0 ≤ (((2 : ℝ) ^ i - 2 ^ j) * ((3 : ℝ) ^ i - 3 ^ j)) := by
  rcases le_total i j with hij | hji
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (pow_le_pow_right₀ (by norm_num) hij))
      (sub_nonpos.mpr (pow_le_pow_right₀ (by norm_num) hij))
  · exact mul_nonneg
      (sub_nonneg.mpr (pow_le_pow_right₀ (by norm_num) hji))
      (sub_nonneg.mpr (pow_le_pow_right₀ (by norm_num) hji))

/-- The pair kernel is strictly positive away from the diagonal. -/
theorem pow_two_three_pair_pos {i j : ℕ} (hij : i ≠ j) :
    0 < (((2 : ℝ) ^ i - 2 ^ j) * ((3 : ℝ) ^ i - 3 ^ j)) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact mul_pos_of_neg_of_neg
      (sub_neg.mpr (pow_lt_pow_right₀ (by norm_num) hij))
      (sub_neg.mpr (pow_lt_pow_right₀ (by norm_num) hij))
  · exact mul_pos
      (sub_pos.mpr (pow_lt_pow_right₀ (by norm_num) hji))
      (sub_pos.mpr (pow_lt_pow_right₀ (by norm_num) hji))

def evalFinite {N : ℕ} (w : Fin N → ℝ) (z : ℝ) : ℝ :=
  ∑ i, w i * z ^ (i : ℕ)

/-- A finite nonnegative coefficient vector with the rank-one values at `1,2,3,6`
has at most one positive coefficient. -/
theorem finite_nonnegative_rankOne_atMostOne
    {N : ℕ} (w : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (h_one : evalFinite w 1 = 1)
    (h_rank : evalFinite w 6 = evalFinite w 2 * evalFinite w 3) :
    ∀ i j, 0 < w i → 0 < w j → i = j := by
  have hsum : ∑ i, w i = 1 := by
    simpa [evalFinite] using h_one
  have hcov := two_mul_covariance_identity w
    (fun i : Fin N => (2 : ℝ) ^ (i : ℕ))
    (fun i : Fin N => (3 : ℝ) ^ (i : ℕ))
  have hsix :
      (∑ i, w i * (2 : ℝ) ^ (i : ℕ) * 3 ^ (i : ℕ)) = evalFinite w 6 := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      w i * (2 : ℝ) ^ (i : ℕ) * 3 ^ (i : ℕ) =
          w i * ((2 : ℝ) ^ (i : ℕ) * 3 ^ (i : ℕ)) := by ring
      _ = w i * ((2 * 3 : ℝ) ^ (i : ℕ)) := by rw [mul_pow]
      _ = w i * (6 : ℝ) ^ (i : ℕ) := by norm_num
  have htwo : (∑ i, w i * (2 : ℝ) ^ (i : ℕ)) = evalFinite w 2 := rfl
  have hthree : (∑ i, w i * (3 : ℝ) ^ (i : ℕ)) = evalFinite w 3 := rfl
  have hkernel_zero :
      (∑ i, ∑ j, w i * w j *
        ((2 : ℝ) ^ (i : ℕ) - 2 ^ (j : ℕ)) *
        ((3 : ℝ) ^ (i : ℕ) - 3 ^ (j : ℕ))) = 0 := by
    rw [← hcov, hsum, hsix, htwo, hthree, h_rank]
    ring
  intro i j hi hj
  by_contra hij
  have hij_nat : (i : ℕ) ≠ (j : ℕ) := by
    intro h
    exact hij (Fin.ext h)
  have hterm_pos :
      0 < w i * w j *
        ((2 : ℝ) ^ (i : ℕ) - 2 ^ (j : ℕ)) *
        ((3 : ℝ) ^ (i : ℕ) - 3 ^ (j : ℕ)) := by
    calc
      0 < (w i * w j) *
          (((2 : ℝ) ^ (i : ℕ) - 2 ^ (j : ℕ)) *
            ((3 : ℝ) ^ (i : ℕ) - 3 ^ (j : ℕ))) :=
        mul_pos (mul_pos hi hj) (pow_two_three_pair_pos hij_nat)
      _ = _ := by ring
  have hterm_le :
      w i * w j *
          ((2 : ℝ) ^ (i : ℕ) - 2 ^ (j : ℕ)) *
          ((3 : ℝ) ^ (i : ℕ) - 3 ^ (j : ℕ)) ≤
        ∑ a, ∑ b, w a * w b *
          ((2 : ℝ) ^ (a : ℕ) - 2 ^ (b : ℕ)) *
          ((3 : ℝ) ^ (a : ℕ) - 3 ^ (b : ℕ)) := by
    have hnonneg (a b : Fin N) :
        0 ≤ w a * w b *
          ((2 : ℝ) ^ (a : ℕ) - 2 ^ (b : ℕ)) *
          ((3 : ℝ) ^ (a : ℕ) - 3 ^ (b : ℕ)) := by
      calc
        0 ≤ (w a * w b) *
            (((2 : ℝ) ^ (a : ℕ) - 2 ^ (b : ℕ)) *
              ((3 : ℝ) ^ (a : ℕ) - 3 ^ (b : ℕ))) :=
          mul_nonneg (mul_nonneg (hw a) (hw b))
            (pow_two_three_pair_nonneg (a : ℕ) (b : ℕ))
        _ = _ := by ring
    have hinner_nonneg (a : Fin N) :
        0 ≤ ∑ b, w a * w b *
          ((2 : ℝ) ^ (a : ℕ) - 2 ^ (b : ℕ)) *
          ((3 : ℝ) ^ (a : ℕ) - 3 ^ (b : ℕ)) :=
      Finset.sum_nonneg fun b _ => hnonneg a b
    have hpair_le_inner :
        w i * w j *
            ((2 : ℝ) ^ (i : ℕ) - 2 ^ (j : ℕ)) *
            ((3 : ℝ) ^ (i : ℕ) - 3 ^ (j : ℕ)) ≤
          ∑ b, w i * w b *
            ((2 : ℝ) ^ (i : ℕ) - 2 ^ (b : ℕ)) *
            ((3 : ℝ) ^ (i : ℕ) - 3 ^ (b : ℕ)) :=
      Finset.single_le_sum (fun b _ => hnonneg i b) (by simp)
    have hinner_le_total :
        (∑ b, w i * w b *
            ((2 : ℝ) ^ (i : ℕ) - 2 ^ (b : ℕ)) *
            ((3 : ℝ) ^ (i : ℕ) - 3 ^ (b : ℕ))) ≤
          ∑ a, ∑ b, w a * w b *
            ((2 : ℝ) ^ (a : ℕ) - 2 ^ (b : ℕ)) *
            ((3 : ℝ) ^ (a : ℕ) - 3 ^ (b : ℕ)) :=
      Finset.single_le_sum (fun a _ => hinner_nonneg a) (by simp)
    exact hpair_le_inner.trans hinner_le_total
  rw [hkernel_zero] at hterm_le
  linarith

/-- The coefficient vector is exactly a unit mass. -/
theorem finite_nonnegative_rankOne_eq_single
    {N : ℕ} (w : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (h_one : evalFinite w 1 = 1)
    (h_rank : evalFinite w 6 = evalFinite w 2 * evalFinite w 3) :
    ∃ n, w n = 1 ∧ ∀ k, k ≠ n → w k = 0 := by
  have hone_support := finite_nonnegative_rankOne_atMostOne w hw h_one h_rank
  have hsum : ∑ i, w i = 1 := by
    simpa [evalFinite] using h_one
  have hsum_pos : 0 < ∑ i, w i := by rw [hsum]; norm_num
  have hex : ∃ n, 0 < w n := by
    rw [Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)] at hsum_pos
    simpa using hsum_pos
  obtain ⟨n, hn⟩ := hex
  have hzero : ∀ k, k ≠ n → w k = 0 := by
    intro k hkn
    have hnpos : ¬0 < w k := by
      intro hk
      exact hkn (hone_support k n hk hn)
    exact ((hw k).eq_of_not_lt hnpos).symm
  have hsum_single : ∑ k, w k = w n := by
    exact Finset.sum_eq_single n
      (fun k _ hkn => hzero k hkn)
      (by simp)
  refine ⟨n, ?_, hzero⟩
  linarith [hsum, hsum_single]

end PositiveCoefficientClosure
end LeanProofs.TwoBaseIntegerExponent
