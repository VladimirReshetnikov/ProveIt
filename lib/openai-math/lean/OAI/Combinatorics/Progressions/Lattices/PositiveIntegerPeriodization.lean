import OAI.Combinatorics.Progressions.Estimates.SeparatedPositiveSum
import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

noncomputable def positiveIntegerPeriodization (H : (D → ℝ) → ℝ) (x : D → ℝ) : ℝ :=
  ∑' n : D → ℤ, H (fun i => x i + (n i : ℝ))

omit [Fintype D] in
theorem integer_shifts_small_box_injective (x : D → ℝ) (n m : D → ℤ)
    (hn : ∀ i, |x i + (n i : ℝ)| < 1/2) (hm : ∀ i, |x i + (m i : ℝ)| < 1/2) : n = m := by
  have he := small_coordinate_lift_unique x (fun i => x i + (n i : ℝ))
    (fun i => x i + (m i : ℝ)) hn hm
    (fun i => ⟨-n i, by push_cast; ring⟩) (fun i => ⟨-m i, by push_cast; ring⟩)
  funext i
  apply Int.cast_injective (α := ℝ)
  have hi := congrFun he i
  linarith

omit [Fintype D] in
theorem positiveIntegerPeriodization_periodic (H : (D → ℝ) → ℝ) (x : D → ℝ) (m : D → ℤ) :
    positiveIntegerPeriodization H (fun i => x i + (m i : ℝ)) = positiveIntegerPeriodization H x := by
  unfold positiveIntegerPeriodization
  have h := (Equiv.addRight m).tsum_eq (fun n : D → ℤ => H (fun i => x i + (n i : ℝ)))
  convert h using 1
  apply tsum_congr
  intro n
  congr 1
  funext i
  change x i + (m i : ℝ) + (n i : ℝ) = x i + ((n i + m i : ℤ) : ℝ)
  push_cast
  ring

omit [Fintype D] in
theorem positiveIntegerPeriodization_local (H : (D → ℝ) → ℝ)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ) (hx : ∀ i, |x i| < 1/2) :
    positiveIntegerPeriodization H x = H x := by
  unfold positiveIntegerPeriodization
  rw [tsum_eq_single (0 : D → ℤ)]
  · simp
  · intro n hn
    by_contra hnonzero
    apply hn
    exact integer_shifts_small_box_injective x n 0 (hs _ hnonzero) (by simpa using hx)

theorem positiveIntegerPeriodization_lipschitz (H : (D → ℝ) → ℝ) {L : ℝ≥0}
    (hH : LipschitzWith L H) (h0 : ∀ x, 0 ≤ H x)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith L (positiveIntegerPeriodization H) := by
  apply separated_tsum_lipschitz
  · intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hH.dist_le_mul (x + fun i => (n i : ℝ)) (y + fun i => (n i : ℝ))
    rw [dist_add_right] at h
    exact h
  · intro n x
    exact h0 _
  · intro x n m hn hm
    exact integer_shifts_small_box_injective x n m (hs _ hn) (hs _ hm)

omit [Fintype D] in
theorem positiveIntegerPeriodization_range (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, 0 ≤ H x ∧ H x ≤ B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ) :
    0 ≤ positiveIntegerPeriodization H x ∧ positiveIntegerPeriodization H x ≤ B := by
  refine ⟨tsum_nonneg (fun n => (hH _).1), ?_⟩
  by_cases hx : ∃ n : D → ℤ, H (fun i => x i + (n i : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hx
    have he : positiveIntegerPeriodization H x = H (fun i => x i + (n i : ℝ)) := by
      apply tsum_eq_single n
      intro m hm
      by_contra hnonzero
      exact hm (integer_shifts_small_box_injective x m n (hs _ hnonzero) (hs _ hn))
    rw [he]
    exact (hH _).2
  · have hz : ∀ n : D → ℤ, H (fun i => x i + (n i : ℝ)) = 0 :=
      fun n => not_ne_iff.mp (fun hn => hx ⟨n, hn⟩)
    simp only [positiveIntegerPeriodization, hz, tsum_zero]
    exact hB

end Erdos3

end

end OAI
