/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Analysis.Normed.Group.Constructions
import OAI.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff
import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracy
import OAI.Combinatorics.Progressions.Geometry.ChartCutoff

namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def coordinateBoxCutoff {ι : Type*} [Fintype ι]
    (χ : ℝ → ℝ) (r : ℝ) (v : ι → ℝ) : ℝ := ∏ i, χ (v i / r)

theorem coordinateBoxCutoff_range {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (r : ℝ) (v : ι → ℝ) :
    0 ≤ coordinateBoxCutoff χ r v ∧ coordinateBoxCutoff χ r v ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (hχ _).1),
    Finset.prod_le_one₀ (fun index _ => (hχ _).1) (fun index _ => (hχ _).2)⟩

theorem coordinateBoxCutoff_eq_one {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, |x| ≤ 1 / 2 → χ x = 1) {r : ℝ} (hr : 0 < r)
    (v : ι → ℝ) (hv : ∀ i, |v i| ≤ r / 2) : coordinateBoxCutoff χ r v = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply hχ
  rw [abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  linarith [hv i]

theorem coordinateBoxCutoff_eq_zero {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, 3 / 4 ≤ |x| → χ x = 0) {r : ℝ} (hr : 0 < r)
    (v : ι → ℝ) (hv : ∃ i, 3 * r / 4 ≤ |v i|) : coordinateBoxCutoff χ r v = 0 := by
  classical
  obtain ⟨i, hi⟩ := hv
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply hχ
  rw [abs_div, abs_of_pos hr]
  apply (le_div_iff₀ hr).mpr
  linarith

theorem contDiff_coordinateBoxCutoff {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (r : ℝ) : ContDiff ℝ ∞ (coordinateBoxCutoff (ι := ι) χ r) := by
  unfold coordinateBoxCutoff
  apply contDiff_prod
  intro i _
  exact hχ.comp ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.div_const r)

theorem hasCompactSupport_coordinateBoxCutoff {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, 3 / 4 ≤ |x| → χ x = 0) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (coordinateBoxCutoff (ι := ι) χ r) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ι → ℝ) (3 * r / 4))
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 3 * r / 4)).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_contra! hi
  exact hv (coordinateBoxCutoff_eq_zero χ hχ hr v ⟨i, hi.le⟩)

theorem lipschitz_coordinateBoxCutoff {ι : Type*} [Fintype ι] (χ : ℝ → ℝ) (A r : ℝ≥0)
    (hr : 0 < r) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hLip : LipschitzWith A χ) :
    LipschitzWith (Fintype.card ι * A / r) (coordinateBoxCutoff (ι := ι) χ r) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have hr' : (0 : ℝ) < r := hr
  have hcoord (i) : |v i - w i| ≤ dist v w := by
    simpa only [Real.dist_eq] using dist_le_pi_dist v w i
  have hd (i) : |χ (v i / r) - χ (w i / r)| ≤ ((A : ℝ) / r) * dist v w := by
    have h := hLip.dist_le_mul (v i / r) (w i / r)
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr'] at h
    apply h.trans
    calc
      (A : ℝ) * (|v i - w i| / r) = ((A : ℝ) / r) * |v i - w i| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcoord i) (by positivity)
  have hprod := abs_finset_prod_sub_prod_le Finset.univ (fun i => χ (v i / r))
    (fun i => χ (w i / r)) (B := 1) (δ := ((A : ℝ) / r) * dist v w) le_rfl (by positivity)
    (fun i _ => by rw [abs_of_nonneg (hχ _).1]; exact (hχ _).2)
    (fun i _ => by rw [abs_of_nonneg (hχ _).1]; exact (hχ _).2) (fun i _ => hd i)
  rw [Real.dist_eq]
  apply hprod.trans_eq
  simp only [Finset.card_univ, one_pow, mul_one, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
  ring

theorem exists_smooth_box_cutoffs :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ {ι : Type*} [Fintype ι] (r : ℝ≥0), 0 < r →
      ∃ ψ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) ∧
        (∀ v, (∀ i, |v i| ≤ (r : ℝ) / 2) → ψ v = 1) ∧
        (∀ v, (∃ i, 3 * (r : ℝ) / 4 ≤ |v i|) → ψ v = 0) ∧
        LipschitzWith (Fintype.card ι * A / r) ψ := by
  obtain ⟨A, hA, χ, hsmooth, hχ, hone, hzero, hLip⟩ := exists_smooth_scalar_cutoff
  refine ⟨A, hA, ?_⟩
  intro ι _ r hr
  exact ⟨coordinateBoxCutoff χ r, contDiff_coordinateBoxCutoff χ hsmooth r,
    hasCompactSupport_coordinateBoxCutoff χ hzero hr,
    coordinateBoxCutoff_range χ hχ r, coordinateBoxCutoff_eq_one χ hone hr,
    coordinateBoxCutoff_eq_zero χ hzero hr, lipschitz_coordinateBoxCutoff χ A r hr hχ hLip⟩

end Erdos3

end

section

namespace Erdos3

open Set

theorem support_subset_box_of_cutoff {ι : Type*} [Fintype ι] (ψ : (ι → ℝ) → ℝ)
    {r : ℝ} (hr : 0 < r) (hzero : ∀ v, (∃ i, 3 * r / 4 ≤ |v i|) → ψ v = 0) :
    Function.support ψ ⊆ Metric.closedBall 0 (3 * r / 4) := by
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 3 * r / 4)).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_contra! hi
  exact hv (hzero v ⟨i, hi.le⟩)

theorem closedBox_subset_chart_source {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (φ : OpenPartialHomeomorph (ι → ℝ) X) {r : ℝ} (hr : 0 < r)
    (hsource : φ.source = {v | ∀ i, |v i| < r}) :
    Metric.closedBall 0 (3 * r / 4) ⊆ φ.source := by
  intro v hv
  rw [hsource]
  intro i
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  have hi := (norm_le_pi_norm v i).trans hv
  rw [Real.norm_eq_abs] at hi
  linarith

theorem boxChartCutoff_support {ι X : Type*} [Fintype ι] [TopologicalSpace X] [T2Space X]
    (φ : OpenPartialHomeomorph (ι → ℝ) X) (ψ : (ι → ℝ) → ℝ) {r : ℝ} (hr : 0 < r)
    (hsource : φ.source = {v | ∀ i, |v i| < r})
    (hzero : ∀ v, (∃ i, 3 * r / 4 ≤ |v i|) → ψ v = 0) :
    HasCompactSupport (chartCutoff φ ψ) ∧ tsupport (chartCutoff φ ψ) ⊆ φ.target := by
  have hS := closedBox_subset_chart_source φ hr hsource
  have hsupport := support_subset_box_of_cutoff ψ hr hzero
  refine ⟨hasCompactSupport_chartCutoff φ ψ (isCompact_closedBall _ _) hS hsupport, ?_⟩
  intro x hx
  obtain ⟨v, hv, rfl⟩ := tsupport_chartCutoff_subset φ ψ (isCompact_closedBall _ _) hS hsupport hx
  exact φ.map_source (hS hv)

theorem boxChartCutoff_eq_one {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (φ : OpenPartialHomeomorph (ι → ℝ) X) (ψ : (ι → ℝ) → ℝ) {r : ℝ} (hr : 0 < r)
    (hsource : φ.source = {v | ∀ i, |v i| < r})
    (hone : ∀ v, (∀ i, |v i| ≤ r / 2) → ψ v = 1) (v : ι → ℝ)
    (hv : ∀ i, |v i| ≤ r / 2) : chartCutoff φ ψ (φ v) = 1 := by
  rw [chartCutoff_apply φ ψ (by rw [hsource]; intro i; linarith [hv i])]
  exact hone v hv

end Erdos3

end

end OAI
