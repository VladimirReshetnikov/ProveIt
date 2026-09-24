import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Dominance of the radical weights in relation combining

For bounds `‖z i‖ + 1 ≤ v i`, the successive prefix products of `v`
separate signed radical sums. The norm of every prefix sum is at most
the next weight minus one. Consequently a zero weighted sum cannot have
a nonzero final term of norm at least one.

These estimates apply to the original common weight and to the refined
individual weights mentioned after Theorem 3.9 of the 1976 article.
-/

namespace Diophantine.RadicalWeights

/-- The weight preceding the radical with index `n`. -/
noncomputable def weight (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, v i

/-- The weighted sum of the first `n` radicals. -/
noncomputable def weightedSum (v : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range n, z i * (weight v i : ℂ)

@[simp] theorem weight_zero (v : ℕ → ℝ) : weight v 0 = 1 := by
  simp [weight]

theorem weight_succ (v : ℕ → ℝ) (n : ℕ) :
    weight v (n + 1) = weight v n * v n := by
  simp [weight, Finset.prod_range_succ]

@[simp] theorem weightedSum_zero (v : ℕ → ℝ) (z : ℕ → ℂ) :
    weightedSum v z 0 = 0 := by
  simp [weightedSum]

theorem weightedSum_succ (v : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) :
    weightedSum v z (n + 1) = weightedSum v z n + z n * (weight v n : ℂ) := by
  simp [weightedSum, Finset.sum_range_succ]

theorem one_le_weight {v : ℕ → ℝ} {n : ℕ}
    (hv : ∀ i < n, 1 ≤ v i) : 1 ≤ weight v n := by
  exact Finset.one_le_prod (fun i hi => hv i (Finset.mem_range.mp hi))

/-- Telescoping prefix bound, including the empty prefix. -/
theorem norm_weightedSum_le {v : ℕ → ℝ} {z : ℕ → ℂ} {n : ℕ}
    (hv : ∀ i < n, 1 ≤ v i) (hz : ∀ i < n, ‖z i‖ ≤ v i - 1) :
    ‖weightedSum v z n‖ ≤ weight v n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hv' : ∀ i < n, 1 ≤ v i := fun i hi => hv i (by omega)
      have hz' : ∀ i < n, ‖z i‖ ≤ v i - 1 := fun i hi => hz i (by omega)
      have hw : 0 ≤ weight v n := le_trans (by norm_num) (one_le_weight hv')
      have hnorm : ‖(weight v n : ℂ)‖ = weight v n := by
        rw [Complex.norm_real, Real.norm_of_nonneg hw]
      rw [weightedSum_succ, weight_succ]
      calc
        ‖weightedSum v z n + z n * (weight v n : ℂ)‖ ≤
            ‖weightedSum v z n‖ + ‖z n * (weight v n : ℂ)‖ := norm_add_le _ _
        _ = ‖weightedSum v z n‖ + ‖z n‖ * weight v n := by rw [norm_mul, hnorm]
        _ ≤ (weight v n - 1) + (v n - 1) * weight v n :=
          add_le_add (ih hv' hz') (mul_le_mul_of_nonneg_right (hz n (by omega)) hw)
        _ = weight v n * v n - 1 := by ring

/-- Weighted radicals of norm at least one cannot cancel, even when some
radicals are replaced by zero. No independence of their square classes is
assumed. -/
theorem eq_zero_of_weightedSum_eq_zero {v : ℕ → ℝ} {z : ℕ → ℂ} {n : ℕ}
    (hv : ∀ i < n, 1 ≤ v i) (hz : ∀ i < n, ‖z i‖ ≤ v i - 1)
    (hgap : ∀ i < n, z i ≠ 0 → 1 ≤ ‖z i‖)
    (hsum : weightedSum v z n = 0) : ∀ i < n, z i = 0 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      have hv' : ∀ i < n, 1 ≤ v i := fun i hi => hv i (by omega)
      have hz' : ∀ i < n, ‖z i‖ ≤ v i - 1 := fun i hi => hz i (by omega)
      have hgap' : ∀ i < n, z i ≠ 0 → 1 ≤ ‖z i‖ :=
        fun i hi => hgap i (by omega)
      have hw : 0 ≤ weight v n := le_trans (by norm_num) (one_le_weight hv')
      have hnorm : ‖(weight v n : ℂ)‖ = weight v n := by
        rw [Complex.norm_real, Real.norm_of_nonneg hw]
      have hlast : z n = 0 := by
        by_contra hn
        have hlow : weight v n ≤ ‖z n * (weight v n : ℂ)‖ := by
          rw [norm_mul, hnorm]
          nlinarith [hgap n (by omega) hn]
        have heq : z n * (weight v n : ℂ) = -weightedSum v z n := by
          rw [weightedSum_succ] at hsum
          exact eq_neg_of_add_eq_zero_right hsum
        rw [heq, norm_neg] at hlow
        have hupp := norm_weightedSum_le hv' hz'
        linarith
      have hprefix : weightedSum v z n = 0 := by
        simpa only [weightedSum_succ, hlast, zero_mul, add_zero] using hsum
      intro i hi
      by_cases hin : i < n
      · exact ih hv' hz' hgap' hprefix i hin
      · have : i = n := by omega
        simpa only [this] using hlast

/-- The offset used in the relation-combining polynomial is positive even
for a signed radical sum. -/
theorem one_le_weight_add_re {v : ℕ → ℝ} {z : ℕ → ℂ} {n : ℕ}
    (hv : ∀ i < n, 1 ≤ v i) (hz : ∀ i < n, ‖z i‖ ≤ v i - 1) :
    1 ≤ weight v n + (weightedSum v z n).re := by
  have h := Complex.re_le_norm (-weightedSum v z n)
  simp only [Complex.neg_re, norm_neg] at h
  have hbound := norm_weightedSum_le hv hz
  linarith

end Diophantine.RadicalWeights
