/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def cappedDistanceTest {X : Type*} [PseudoMetricSpace X] (a x : X) : ℂ :=
  (min 1 (dist a x) : ℝ)

theorem cappedDistanceTest_unit_interval {X : Type*} [PseudoMetricSpace X] (a x : X) :
    (cappedDistanceTest a x).im = 0 ∧ 0 ≤ (cappedDistanceTest a x).re ∧
      (cappedDistanceTest a x).re ≤ 1 :=
  ⟨rfl, le_min zero_le_one dist_nonneg, min_le_left _ _⟩

theorem cappedDistanceTest_lipschitz {X : Type*} [PseudoMetricSpace X] (a : X) :
    LipschitzWith 1 (cappedDistanceTest a) := by
  unfold cappedDistanceTest
  simpa only [one_mul, Function.comp_def] using
    Complex.isometry_ofReal.lipschitzWith.comp ((LipschitzWith.dist_right a).const_min 1)

theorem local_dist_le_of_positive_reconstruction {A X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : A → X) (g : A → Y) (L : ℝ≥0)
    (hrec : ∀ a : X, ∃ (v : Y → ℂ) (K : ℝ≥0), K ≤ L ∧ LipschitzWith K v ∧
      ∀ x, v (g x) = cappedDistanceTest a (f x))
    (x y : A) (hnear : (L : ℝ) * dist (g x) (g y) < 1) :
    dist (f x) (f y) ≤ L * dist (g x) (g y) := by
  obtain ⟨v, K, hK, hv, heval⟩ := hrec (f x)
  have hmin : min 1 (dist (f x) (f y)) ≤ (L : ℝ) * dist (g x) (g y) := by
    have h := hv.dist_le_mul (g y) (g x)
    rw [heval, heval] at h
    simpa only [cappedDistanceTest, dist_self, min_eq_right zero_le_one,
      Complex.ofReal_zero, dist_zero_right, dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_min zero_le_one dist_nonneg), dist_comm] using
      h.trans (mul_le_mul_of_nonneg_right (show (K : ℝ) ≤ L from hK) dist_nonneg)
  have hdist : dist (f x) (f y) < 1 := by
    by_contra h
    rw [min_eq_left (le_of_not_gt h)] at hmin
    linarith
  simpa only [min_eq_right hdist.le] using hmin

end Erdos3

end

end OAI
