import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Algebra.Polynomial.Splits

/-!
# The least maximal coefficient counts the roots in a strict disk

For a polynomial over an ultrametric normed field and radius r > 0, the
least index maximizing ‖P.coeff i‖ * r^i is additive under multiplication.
Each factor X - a then contributes one exactly when ‖a‖ < r. This is the
strict-disk rule used in smd:lem:newton, including ties at the boundary.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators Classical
open Polynomial

variable {K : Type*} [NormedField K]

/-- The weighted coefficient norm used by the Gauss norm at radius r. -/
noncomputable def weightedCoeffNorm (P : Polynomial K) (r : ℝ) (i : ℕ) : ℝ :=
  ‖P.coeff i‖ * r ^ i

/-- Index i attains a positive maximum, and every lower index is strictly
below that maximum. -/
structure IsLeastMaximalCoeff (P : Polynomial K) (r : ℝ) (i : ℕ) : Prop where
  pos : 0 < weightedCoeffNorm P r i
  le_max : ∀ k, weightedCoeffNorm P r k ≤ weightedCoeffNorm P r i
  lt_of_lt : ∀ k < i, weightedCoeffNorm P r k < weightedCoeffNorm P r i

theorem IsLeastMaximalCoeff.unique {P : Polynomial K} {r : ℝ} {i j : ℕ}
    (hi : IsLeastMaximalCoeff P r i) (hj : IsLeastMaximalCoeff P r j) : i = j := by
  apply le_antisymm
  · by_contra! h
    exact (not_lt_of_ge (hj.le_max i)) (hi.lt_of_lt j h)
  · by_contra! h
    exact (not_lt_of_ge (hi.le_max j)) (hj.lt_of_lt i h)

private theorem weightedCoeffNorm_nonneg (P : Polynomial K) {r : ℝ} (hr : 0 ≤ r) (i : ℕ) :
    0 ≤ weightedCoeffNorm P r i :=
  mul_nonneg (norm_nonneg _) (pow_nonneg hr _)

theorem exists_isLeastMaximalCoeff (P : Polynomial K) (hP : P ≠ 0)
    {r : ℝ} (hr : 0 < r) : ∃ i, IsLeastMaximalCoeff P r i := by
  let v := NormedField.toMulRingNorm K
  obtain ⟨i, hi, hlt⟩ := P.exists_min_eq_gaussNorm v hr.le
  change P.gaussNorm v r = weightedCoeffNorm P r i at hi
  refine ⟨i, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Polynomial.support_nonempty.mpr hP
    rw [← hi]
    exact (mul_pos (norm_pos_iff.mpr (mem_support_iff.mp hk)) (pow_pos hr k)).trans_le
      (P.le_gaussNorm v hr.le k)
  · intro k
    rw [← hi]
    exact P.le_gaussNorm v hr.le k
  · intro k hk
    rw [← hi]
    exact hlt k hk

private theorem weighted_convolution_term (P Q : Polynomial K) (r : ℝ) {k j : ℕ} (hj : j ≤ k) :
    ‖P.coeff j * Q.coeff (k - j)‖ * r ^ k =
      weightedCoeffNorm P r j * weightedCoeffNorm Q r (k - j) := by
  have hpow : r ^ j * r ^ (k - j) = r ^ k := by rw [← pow_add, Nat.add_sub_of_le hj]
  simp only [weightedCoeffNorm, norm_mul]
  rw [mul_mul_mul_comm, hpow]

section
variable [IsUltrametricDist K]

private theorem weighted_coeff_mul_le_some (P Q : Polynomial K) {r : ℝ} (hr : 0 ≤ r)
    (k : ℕ) : ∃ j ≤ k, weightedCoeffNorm (P * Q) r k ≤
      weightedCoeffNorm P r j * weightedCoeffNorm Q r (k - j) := by
  obtain ⟨j, hj, h⟩ := IsNonarchimedean.finset_image_add_of_nonempty
    (IsUltrametricDist.norm_add_le_max (S := K)) (fun j => P.coeff j * Q.coeff (k - j))
    (Finset.nonempty_range_add_one (n := k))
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  refine ⟨j, hj', ?_⟩
  rw [weightedCoeffNorm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← weighted_convolution_term P Q r hj']
  exact mul_le_mul_of_nonneg_right h (pow_nonneg hr k)

/-- The first maximal index is additive under polynomial multiplication. -/
theorem IsLeastMaximalCoeff.mul {P Q : Polynomial K} {r : ℝ} {i j : ℕ}
    (hP : IsLeastMaximalCoeff P r i) (hQ : IsLeastMaximalCoeff Q r j)
    (hr : 0 < r) : IsLeastMaximalCoeff (P * Q) r (i + j) := by
  let M := weightedCoeffNorm P r i * weightedCoeffNorm Q r j
  have hlt (k l : ℕ) (h : l < i ∨ k - l < j) :
      weightedCoeffNorm P r l * weightedCoeffNorm Q r (k - l) < M := by
    rcases h with h | h
    · exact (mul_le_mul_of_nonneg_left (hQ.le_max _) (weightedCoeffNorm_nonneg P hr.le _)).trans_lt
        (mul_lt_mul_of_pos_right (hP.lt_of_lt _ h) hQ.pos)
    · exact (mul_le_mul_of_nonneg_right (hP.le_max _) (weightedCoeffNorm_nonneg Q hr.le _)).trans_lt
        (mul_lt_mul_of_pos_left (hQ.lt_of_lt _ h) hP.pos)
  have hterm : ‖P.coeff i * Q.coeff (i + j - i)‖ * r ^ (i + j) = M := by
    rw [weighted_convolution_term P Q r (by omega : i ≤ i + j), Nat.add_sub_cancel_left]
  have hmax (l : ℕ) (hl : l ∈ Finset.range (i + j + 1)) (hne : l ≠ i) :
      ‖P.coeff l * Q.coeff (i + j - l)‖ < ‖P.coeff i * Q.coeff (i + j - i)‖ := by
    have hl' := Finset.mem_range.mp hl
    apply lt_of_mul_lt_mul_right _ (pow_nonneg hr.le (i + j))
    rw [weighted_convolution_term P Q r (by omega : l ≤ i + j), hterm]
    exact hlt _ _ (by omega)
  have hEq : weightedCoeffNorm (P * Q) r (i + j) = M := by
    rw [weightedCoeffNorm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [IsNonarchimedean.apply_sum_eq_of_lt
      (IsUltrametricDist.norm_add_le_max (S := K)) (fun x => (norm_neg x).symm)
      (k := i) (by simp) hmax]
    exact hterm
  refine ⟨hEq.symm ▸ mul_pos hP.pos hQ.pos, ?_, ?_⟩
  · intro k
    obtain ⟨l, hl, hle⟩ := weighted_coeff_mul_le_some P Q hr.le k
    rw [hEq]
    exact hle.trans (mul_le_mul (hP.le_max _) (hQ.le_max _)
      (weightedCoeffNorm_nonneg Q hr.le _) hP.pos.le)
  · intro k hk
    obtain ⟨l, hl, hle⟩ := weighted_coeff_mul_le_some P Q hr.le k
    rw [hEq]
    exact hle.trans_lt (hlt _ _ (by omega))

end

theorem isLeastMaximalCoeff_C (a : K) (ha : a ≠ 0) (r : ℝ) :
    IsLeastMaximalCoeff (C a) r 0 := by
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr ha
  refine ⟨by simpa [weightedCoeffNorm] using hp, ?_, by omega⟩
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simp [weightedCoeffNorm, coeff_C, hk, hp.le]

/-- In the tied case ‖a‖ = r the constant term is the first maximum. -/
theorem isLeastMaximalCoeff_X_sub_C (a : K) {r : ℝ} (hr : 0 < r) :
    IsLeastMaximalCoeff (X - C a) r (if ‖a‖ < r then 1 else 0) := by
  have h0 : weightedCoeffNorm (X - C a) r 0 = ‖a‖ := by simp [weightedCoeffNorm, coeff_sub]
  have h1 : weightedCoeffNorm (X - C a) r 1 = r := by simp [weightedCoeffNorm, coeff_sub]
  have hz (k : ℕ) (hk : k ≠ 0) (hk' : k ≠ 1) :
      weightedCoeffNorm (X - C a) r k = 0 := by
    simp [weightedCoeffNorm, coeff_sub, coeff_X, coeff_C, hk, Ne.symm hk']
  by_cases h : ‖a‖ < r
  · rw [if_pos h]
    refine ⟨h1.symm ▸ hr, ?_, ?_⟩
    · intro k
      rw [h1]
      by_cases hk : k = 0
      · simpa [hk, h0] using h.le
      by_cases hk' : k = 1
      · simp [hk', h1]
      · rw [hz _ hk hk']
        exact hr.le
    · intro k hk
      have : k = 0 := by omega
      simpa [this, h0, h1] using h
  · rw [if_neg h]
    refine ⟨h0.symm ▸ (hr.trans_le (not_lt.mp h)), ?_, by omega⟩
    intro k
    by_cases hk : k = 0
    · simp [hk]
    by_cases hk' : k = 1
    · simpa [hk', h0, h1] using not_lt.mp h
    · rw [h0, hz _ hk hk']
      exact norm_nonneg a

variable [IsUltrametricDist K]

theorem isLeastMaximalCoeff_multiset_prod_linear (s : Multiset K) {r : ℝ} (hr : 0 < r) :
    IsLeastMaximalCoeff (s.map (fun a => X - C a)).prod r
      (s.filter (fun a => ‖a‖ < r)).card := by
  induction s using Multiset.induction_on with
  | empty => simpa using isLeastMaximalCoeff_C (K := K) 1 one_ne_zero r
  | cons a s ih =>
    have h := (isLeastMaximalCoeff_X_sub_C a hr).mul ih hr
    by_cases ha : ‖a‖ < r
    · simpa [ha, Nat.add_comm] using h
    · simpa [ha] using h

/-- The least weighted maximal index counts the split roots strictly within
the radius, with multiplicity. -/
theorem isLeastMaximalCoeff_card_roots {P : Polynomial K} (hP : P ≠ 0) (hsplit : P.Splits)
    {r : ℝ} (hr : 0 < r) :
    IsLeastMaximalCoeff P r (P.roots.filter (fun a => ‖a‖ < r)).card := by
  have h := (isLeastMaximalCoeff_C P.leadingCoeff (leadingCoeff_ne_zero.mpr hP) r).mul
    (isLeastMaximalCoeff_multiset_prod_linear P.roots hr) hr
  rw [← hsplit.eq_prod_roots, Nat.zero_add] at h
  exact h

/-- Exact strict-disk count for every least weighted maximal coefficient
index, including when several coefficients share the maximum. -/
theorem eq_card_roots_of_isLeastMaximalCoeff {P : Polynomial K} {r : ℝ} {i : ℕ}
    (hP : P ≠ 0) (hsplit : P.Splits) (hr : 0 < r) (hi : IsLeastMaximalCoeff P r i) :
    i = (P.roots.filter (fun a => ‖a‖ < r)).card :=
  hi.unique (isLeastMaximalCoeff_card_roots hP hsplit hr)

end GRHArticle.SingularModuli
