import MoserWorm.Common.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.SplitIfs

/-! Completed-prefix telescoping and the resulting path-length bound. -/

noncomputable section

namespace MoserWorm.UpperBound

open Finset

/-- Sum of the coefficients whose vertices have already been visited.
Labels at the same vertex enter together. -/
def prefixForce {ι : Type*} [Fintype ι] (f : ι → Plane) (rank : ι → ℕ)
    (j : ℕ) : Plane :=
  ∑ l with rank l ≤ j, f l

private theorem tail_telescope (v : ℕ → Plane) {r m : ℕ} (h : r ≤ m) :
    (∑ j ∈ range m, if r ≤ j then v (j + 1) - v j else 0) = v m - v r := by
  rw [← sum_filter]
  have he : (range m).filter (fun j => r ≤ j) = Ico r m := by
    ext j
    simp [and_comm]
  rw [he]
  exact sum_Ico_sub v h

/-- Discrete integration by parts for finitely many labelled contacts.
Unlabelled vertices and coincident labels are allowed. -/
theorem completed_prefix_telescope {ι : Type*} [Fintype ι]
    (f : ι → Plane) (rank : ι → ℕ) (v : ℕ → Plane) (m : ℕ)
    (hrank : ∀ l, rank l ≤ m) (hbalance : ∑ l, f l = 0) :
    (∑ l, inner ℝ (f l) (v (rank l))) =
      ∑ j ∈ range m, inner ℝ (-prefixForce f rank j) (v (j + 1) - v j) := by
  classical
  have hswap :
      (∑ j ∈ range m, inner ℝ (prefixForce f rank j) (v (j + 1) - v j)) =
        ∑ l, inner ℝ (f l) (v m - v (rank l)) := by
    simp only [prefixForce, sum_inner, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro l _
    calc
      (∑ j ∈ range m, inner ℝ (if rank l ≤ j then f l else 0)
          (v (j + 1) - v j)) =
          inner ℝ (f l) (∑ j ∈ range m,
            if rank l ≤ j then v (j + 1) - v j else 0) := by
        rw [inner_sum]
        apply sum_congr rfl
        intro j _
        split_ifs <;> simp
      _ = inner ℝ (f l) (v m - v (rank l)) := by rw [tail_telescope v (hrank l)]
  calc
    (∑ l, inner ℝ (f l) (v (rank l))) =
        -(∑ l, inner ℝ (f l) (v m - v (rank l))) := by
      simp only [inner_sub_right, sum_sub_distrib, ← sum_inner, hbalance,
        inner_zero_left, zero_sub, neg_neg]
    _ = ∑ j ∈ range m,
        inner ℝ (-prefixForce f rank j) (v (j + 1) - v j) := by
      rw [← hswap, ← sum_neg_distrib]
      simp only [inner_neg_left]

/-- Unit bounds on completed-prefix coefficient sums bound the weighted
contact functional by the open visiting-path length. -/
theorem completed_prefix_length_bound {ι : Type*} [Fintype ι]
    (f : ι → Plane) (rank : ι → ℕ) (v : ℕ → Plane) (m : ℕ)
    (hrank : ∀ l, rank l ≤ m) (hbalance : ∑ l, f l = 0)
    (hprefix : ∀ j < m, ‖prefixForce f rank j‖ ≤ 1) :
    (∑ l, inner ℝ (f l) (v (rank l))) ≤
      ∑ j ∈ range m, dist (v j) (v (j + 1)) := by
  rw [completed_prefix_telescope f rank v m hrank hbalance]
  apply sum_le_sum
  intro j hj
  calc
    inner ℝ (-prefixForce f rank j) (v (j + 1) - v j) ≤
        ‖-prefixForce f rank j‖ * ‖v (j + 1) - v j‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖v (j + 1) - v j‖ := by
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_right (hprefix j (mem_range.mp hj)) (norm_nonneg _)
    _ = dist (v j) (v (j + 1)) := by rw [one_mul, dist_eq_norm, norm_sub_rev]

/-- A set and its complement have opposite force sums when total force is zero. -/
theorem norm_sum_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Plane) (S : Finset ι) (hbalance : ∑ l, f l = 0) :
    ‖∑ l ∈ Sᶜ, f l‖ = ‖∑ l ∈ S, f l‖ := by
  have h : (∑ l ∈ S, f l) + ∑ l ∈ Sᶜ, f l = 0 := by
    rw [sum_add_sum_compl, hbalance]
  have he : (∑ l ∈ Sᶜ, f l) = -(∑ l ∈ S, f l) := eq_neg_of_add_eq_zero_right h
  rw [he, norm_neg]

end MoserWorm.UpperBound
