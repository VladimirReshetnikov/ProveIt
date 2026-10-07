/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def positiveClip (z : ℂ) : ℂ := (max 0 (min 1 z.re) : ℝ)

theorem positiveClip_unit_interval (z : ℂ) :
    (positiveClip z).im = 0 ∧ 0 ≤ (positiveClip z).re ∧ (positiveClip z).re ≤ 1 := by
  refine ⟨rfl, le_max_left _ _, ?_⟩
  exact max_le (by norm_num) (min_le_left _ _)

theorem positiveClip_eq_self (z : ℂ) (hz : z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1) :
    positiveClip z = z := by
  apply Complex.ext
  · change max 0 (min 1 z.re) = z.re
    rw [min_eq_right hz.2.2, max_eq_right hz.2.1]
  · exact hz.1.symm

theorem positiveClip_lipschitz : LipschitzWith 1 positiveClip := by
  change LipschitzWith 1 (fun z : ℂ => ((max 0 (min 1 z.re) : ℝ) : ℂ))
  have h : LipschitzWith 1 (fun z : ℂ => max 0 (min 1 z.re)) :=
    ((RCLike.lipschitzWith_re (K := ℂ)).const_min 1).const_max 0
  simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp h

theorem norm_positiveClip_le_one (z : ℂ) : ‖positiveClip z‖ ≤ 1 := by
  change ‖((max 0 (min 1 z.re) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  exact (positiveClip_unit_interval z).2.2

theorem norm_positiveClip_sub_le (z c : ℂ)
    (hc : c.im = 0 ∧ 0 ≤ c.re ∧ c.re ≤ 1) :
    ‖positiveClip z - c‖ ≤ ‖z - c‖ := by
  have h := positiveClip_lipschitz.dist_le_mul z c
  simpa only [positiveClip_eq_self c hc, NNReal.coe_one, one_mul, dist_eq_norm] using h

theorem exists_positive_lipschitz_reconstruction {X Y : Type*} [PseudoMetricSpace Y]
    (f : X → ℂ) (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1)
    (φ : X → Y) (v : Y → ℂ) {K : ℝ≥0} (hv : LipschitzWith K v)
    (heval : ∀ x, v (φ x) = f x) :
    ∃ u : Y → ℂ, LipschitzWith K u ∧
      (∀ y, (u y).im = 0 ∧ 0 ≤ (u y).re ∧ (u y).re ≤ 1) ∧
      (∀ y, ‖u y‖ ≤ 1) ∧ ∀ x, u (φ x) = f x := by
  refine ⟨fun y => positiveClip (v y), ?_, fun y => positiveClip_unit_interval (v y),
    fun y => norm_positiveClip_le_one (v y), ?_⟩
  · simpa only [one_mul, Function.comp_def] using positiveClip_lipschitz.comp hv
  · intro x
    change positiveClip (v (φ x)) = f x
    rw [heval, positiveClip_eq_self _ (hf x)]

end Erdos3

end

end OAI
