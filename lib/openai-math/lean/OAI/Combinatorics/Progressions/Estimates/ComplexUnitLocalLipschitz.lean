import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem separated_complex_tsum_lipschitz {ι X : Type*} [PseudoMetricSpace X]
    (f : ι → X → ℂ) {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (hsep : ∀ x i j, f i x ≠ 0 → f j x ≠ 0 → i = j) :
    LipschitzWith (2 * K) (fun x => ∑' i, f i x) := by
  have hsingle (x : X) (i : ι) (hi : f i x ≠ 0) : (∑' j, f j x) = f i x := by
    apply tsum_eq_single i
    intro j hji
    by_contra hj
    exact hji (hsep x j i hj hi)
  have hzero (x : X) (hx : ¬∃ i, f i x ≠ 0) : (∑' i, f i x) = 0 := by
    have hz : ∀ i, f i x = 0 := fun i => not_ne_iff.mp (fun hi => hx ⟨i, hi⟩)
    simp only [hz, tsum_zero]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hK : (K : ℝ) * dist x y ≤ (2 * K : ℝ≥0) * dist x y := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    nlinarith [K.coe_nonneg, dist_nonneg (x := x) (y := y)]
  by_cases hx : ∃ i, f i x ≠ 0
  · obtain ⟨i, hi⟩ := hx
    rw [hsingle x i hi]
    by_cases hy : ∃ j, f j y ≠ 0
    · obtain ⟨j, hj⟩ := hy
      rw [hsingle y j hj]
      by_cases hij : i = j
      · subst j
        exact ((hf i).dist_le_mul x y).trans hK
      · have hiy : f i y = 0 := by
          by_contra h
          exact hij (hsep y i j h hj)
        have hjx : f j x = 0 := by
          by_contra h
          exact hij (hsep x i j hi h)
        have h1 := (hf i).dist_le_mul x y
        have h2 := (hf j).dist_le_mul x y
        rw [hiy] at h1
        rw [hjx] at h2
        have ht := dist_triangle (f i x) 0 (f j y)
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        linarith
    · rw [hzero y hy]
      have hiy : f i y = 0 := not_ne_iff.mp (fun h => hy ⟨i, h⟩)
      simpa only [hiy] using ((hf i).dist_le_mul x y).trans hK
  · rw [hzero x hx]
    by_cases hy : ∃ j, f j y ≠ 0
    · obtain ⟨j, hj⟩ := hy
      rw [hsingle y j hj]
      have hjx : f j x = 0 := not_ne_iff.mp (fun h => hx ⟨j, h⟩)
      simpa only [hjx] using ((hf j).dist_le_mul x y).trans hK
    · rw [hzero y hy, dist_self]
      positivity

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem lipschitzWith_of_complex_unit_near {X : Type*} [PseudoMetricSpace X]
    (f : X → ℂ) (C L : ℝ≥0) (hbound : ∀ x, ‖f x‖ ≤ 1)
    (hnear : ∀ x y, (C : ℝ) * dist x y < 1 →
      ‖f x - f y‖ ≤ (L : ℝ) * dist x y) :
    LipschitzWith (max (2 * C) L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  by_cases hclose : (C : ℝ) * dist x y < 1
  · exact (hnear x y hclose).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right (2 * C) L) dist_nonneg)
  · have hxy : ‖f x - f y‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hbound x, hbound y])
    have hfar : 2 ≤ ((2 * C : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      linarith [le_of_not_gt hclose]
    exact hxy.trans (hfar.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_left (2 * C) L) dist_nonneg))

end Erdos3

end

end OAI
