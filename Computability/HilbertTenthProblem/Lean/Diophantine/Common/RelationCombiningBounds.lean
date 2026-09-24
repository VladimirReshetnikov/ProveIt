import Diophantine.Common.RadicalBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The common weight and the positive integer offset

The original relation-combining polynomial uses `W = 1 + ∑ Aᵢ²`.
These bounds apply to signed integer radicands and to every choice of
integer square roots, including the empty family.
-/

namespace Diophantine.RelationCombiningBounds

/-- The common weight in the original Matiyasevich--Robinson product. -/
def weight {q : ℕ} (A : Fin q → ℤ) : ℤ := 1 + ∑ i, A i ^ 2

theorem one_le_weight {q : ℕ} (A : Fin q → ℤ) : 1 ≤ weight A := by
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (A i))
  dsimp [weight]
  omega

theorem sq_le_weight_sub_one {q : ℕ} (A : Fin q → ℤ) (i : Fin q) :
    A i ^ 2 ≤ weight A - 1 := by
  simpa [weight] using
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (A j))
      (Finset.mem_univ i))

/-- The norm of any complex root fits the common weight. -/
theorem norm_root_le {q : ℕ} {A : Fin q → ℤ} {r : Fin q → ℂ}
    (hr : ∀ i, r i ^ 2 = (A i : ℂ)) (i : Fin q) :
    ‖r i‖ ≤ (weight A : ℝ) - 1 := by
  have h := RadicalBounds.norm_le_sq_of_sq_eq_int (hr i)
  have hAi : (A i : ℝ) ^ 2 ≤ (weight A : ℝ) - 1 := by
    exact_mod_cast sq_le_weight_sub_one A i
  exact h.trans hAi

/-- Every integer square root, with either sign, fits the common weight. -/
theorem abs_root_le {q : ℕ} {A r : Fin q → ℤ}
    (hr : ∀ i, r i ^ 2 = A i) (i : Fin q) : |r i| ≤ weight A - 1 := by
  have hroot : |r i| ≤ r i ^ 2 := by
    simpa only [Int.natCast_natAbs] using Int.natAbs_le_self_sq (r i)
  rw [hr i] at hroot
  exact hroot.trans ((Int.le_self_sq (A i)).trans (sq_le_weight_sub_one A i))

private theorem one_le_offset_range {W : ℤ} {r : ℕ → ℤ} {n : ℕ}
    (hW : 1 ≤ W) (hr : ∀ i < n, |r i| ≤ W - 1) :
    1 ≤ W ^ n + ∑ i ∈ Finset.range n, r i * W ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprefix := ih (fun i hi => hr i (by omega))
      have hlast := (abs_le.mp (hr n (by omega))).1
      have hpow : 0 ≤ W ^ n := pow_nonneg (by omega) n
      have hmul := mul_nonneg (show 0 ≤ r n + (W - 1) by omega) hpow
      rw [pow_succ, Finset.sum_range_succ]
      nlinarith

/-- The offset is positive for every signed integer choice of roots. -/
theorem one_le_offset {q : ℕ} {A r : Fin q → ℤ}
    (hr : ∀ i, r i ^ 2 = A i) :
    1 ≤ weight A ^ q + ∑ i, r i * weight A ^ i.val := by
  let r' : ℕ → ℤ := fun i => if hi : i < q then r ⟨i, hi⟩ else 0
  have hbound : ∀ i < q, |r' i| ≤ weight A - 1 := by
    intro i hi
    simpa only [r', dif_pos hi] using abs_root_le hr ⟨i, hi⟩
  have h := one_le_offset_range (one_le_weight A) hbound
  rw [Finset.sum_range] at h
  simpa [r'] using h

end Diophantine.RelationCombiningBounds
