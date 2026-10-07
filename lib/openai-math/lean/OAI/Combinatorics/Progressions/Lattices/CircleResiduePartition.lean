import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter

namespace OAI

section

namespace Erdos3.CircleFourier

open scoped NNReal

theorem one_le_mul_dist_toAddCircle {q : ℕ} [NeZero q] {j k : ZMod q} (hjk : j ≠ k) :
    1 ≤ (q : ℝ) * dist (ZMod.toAddCircle j) (ZMod.toAddCircle k) := by
  let z := j - k
  have hz : z ≠ 0 := sub_ne_zero.mpr hjk
  have hzval : 0 < z.val := Nat.pos_of_ne_zero (fun h => hz ((ZMod.val_eq_zero z).mp h))
  have hzlt := z.val_lt
  have hmin : 1 ≤ min z.val (q - z.val) := le_min hzval (by omega)
  have hdist : dist (ZMod.toAddCircle j) (ZMod.toAddCircle k) =
      ((min z.val (q - z.val) : ℕ) : ℝ) / q := by
    rw [dist_eq_norm, ← map_sub, ZMod.toAddCircle_apply]
    have hn := AddCircle.norm_div_natCast (p := (1 : ℝ)) (m := z.val) (n := q)
    simpa only [mul_one, one_mul, Nat.mod_eq_of_lt z.val_lt] using hn
  rw [hdist, mul_div_cancel₀ _ (show (q : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne q))]
  exact_mod_cast hmin

noncomputable def residueCutoff {q : ℕ} [NeZero q] (j : ZMod q) (x : Circle) : ℝ :=
  max 0 (1 - (q : ℝ) * dist x (ZMod.toAddCircle j))

theorem residueCutoff_unit_interval {q : ℕ} [NeZero q] (j : ZMod q) (x : Circle) :
    0 ≤ residueCutoff j x ∧ residueCutoff j x ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  linarith [mul_nonneg (Nat.cast_nonneg q) (dist_nonneg (x := x) (y := ZMod.toAddCircle j))]

theorem residueCutoff_lipschitz {q : ℕ} [NeZero q] (j : ZMod q) :
    LipschitzWith (q : ℝ≥0) (residueCutoff j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |max 0 (1 - (q : ℝ) * dist x (ZMod.toAddCircle j)) -
    max 0 (1 - (q : ℝ) * dist y (ZMod.toAddCircle j))| ≤ (q : ℝ) * dist x y
  calc
    _ ≤ |(1 - (q : ℝ) * dist x (ZMod.toAddCircle j)) -
        (1 - (q : ℝ) * dist y (ZMod.toAddCircle j))| := by
      rw [max_comm 0 _, max_comm 0 _]
      exact abs_max_sub_max_le_abs _ _ _
    _ = (q : ℝ) * |dist x (ZMod.toAddCircle j) - dist y (ZMod.toAddCircle j)| := by
      rw [show (1 - (q : ℝ) * dist x (ZMod.toAddCircle j)) -
          (1 - (q : ℝ) * dist y (ZMod.toAddCircle j)) =
          -(q : ℝ) * (dist x (ZMod.toAddCircle j) - dist y (ZMod.toAddCircle j)) by ring,
        abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg q)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_dist_sub_le x y (ZMod.toAddCircle j)) (Nat.cast_nonneg q)

theorem residueCutoff_at_grid {q : ℕ} [NeZero q] (j k : ZMod q) :
    residueCutoff j (ZMod.toAddCircle k) = if k = j then 1 else 0 := by
  classical
  by_cases h : k = j
  · subst k
    simp [residueCutoff]
  · simp only [h, ↓reduceIte]
    exact max_eq_left (by linarith [one_le_mul_dist_toAddCircle h])

theorem sum_residueCutoff_at_grid {q : ℕ} [NeZero q] (k : ZMod q) :
    ∑ j : ZMod q, residueCutoff j (ZMod.toAddCircle k) = 1 := by
  classical
  simp [residueCutoff_at_grid]

theorem residueCutoff_positive_iff {q : ℕ} [NeZero q] (j k : ZMod q) :
    0 < residueCutoff j (ZMod.toAddCircle k) ↔ k = j := by
  classical
  rw [residueCutoff_at_grid]
  split_ifs <;> simp_all

end Erdos3.CircleFourier

end

end OAI
