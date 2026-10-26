import Diophantine.Common.PellInt

/-! Positive first-order Pell recurrences are monotone in the parameter.
This avoids exponential comparison bounds in index comparisons. -/
namespace DiophantineConsistency.PellBaseMonotonicity

open Pell

/-- Both Pell coordinates increase weakly when the base increases. -/
theorem coordinates_mono_base {A B : ℕ} (hA : 1 < A) (hB : 1 < B)
    (hAB : A ≤ B) (n : ℕ) :
    xn hA n ≤ xn hB n ∧ yn hA n ≤ yn hB n := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact ⟨Nat.add_le_add (Nat.mul_le_mul ih.1 hAB)
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul hAB hAB) 1) ih.2),
      Nat.add_le_add ih.1 (Nat.mul_le_mul ih.2 hAB)⟩

/-- Reverse comparison of second coordinates forces reverse comparison
of their indices, even when the base inequality is not strict. -/
theorem index_lt_of_coordinate_lt {A B p n : ℕ}
    (hA : 1 < A) (hB : 1 < B) (hAB : A ≤ B)
    (h : yn hB n < yn hA p) : n < p := by
  exact (strictMono_y hB).lt_iff_lt.mp
    (h.trans_le (coordinates_mono_base hA hB hAB p).2)

/-- A strengthened version of NativePellBootstrap.main_index_gt_first. -/
theorem main_index_gt_first_of_base_le {A P c k p n : ℕ}
    (hA : 1 < A) (hP : 1 < P) (hAP : A ≤ P)
    (hcp : c = yn hA p) (hk : k = 2 * yn hP n) (hkc : k < c) : n < p := by
  apply index_lt_of_coordinate_lt hA hP hAP
  rw [hcp, hk] at hkc
  omega

/-- The old public statement is retained as a short compatibility wrapper. -/
theorem main_index_gt_first_compatible {A P c k p n : ℕ}
    (hA : 1 < A) (hP : 1 < P) (hc : 1 < c)
    (hp : 0 < p) (hn : 0 < n) (hAP : 2 * A < 2 * P - 1)
    (hcp : c = yn hA p) (hk : k = 2 * yn hP n) (hkc : k < c) : n < p := by
  exact main_index_gt_first_of_base_le hA hP (by omega) hcp hk hkc

end DiophantineConsistency.PellBaseMonotonicity
