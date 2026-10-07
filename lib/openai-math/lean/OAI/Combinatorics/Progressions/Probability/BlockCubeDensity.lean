import OAI.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight

namespace OAI

section

namespace Erdos3

open MeasureTheory

def blockCubeDomain (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] [DecidableEq α] :
    Set (BlockParameter B F α → ℝ) :=
  (blockCubeFlatten B F α).symm ⁻¹' scalarCubeProductDomain (B × F) α

theorem blockCubeDomain_measurable (B F α : Type*) [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] : MeasurableSet (blockCubeDomain B F α) :=
  (MeasurableSet.univ_pi (fun _ => (scalarCubeDomain_isOpen α).measurableSet)).preimage
    (blockCubeFlatten B F α).symm.continuous.measurable

theorem blockCubeDomain_box {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] {a : BlockParameter B F α → ℝ} (ha : a ∈ blockCubeDomain B F α)
    (z : BlockParameter B F α) : |a z| ≤ 1 := by
  have h := blockCubeFlatten_box ha z
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

theorem blockCubeDomain_volume_ne_top (B F α : Type*) [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] : volume (blockCubeDomain B F α) ≠ ⊤ := by
  have hb : blockCubeDomain B F α ⊆ Metric.closedBall (0 : BlockParameter B F α → ℝ) 1 := by
    intro a ha
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro z
    simpa only [Real.norm_eq_abs] using blockCubeDomain_box ha z
  exact ne_of_lt ((measure_mono hb).trans_lt (isCompact_closedBall _ _).measure_lt_top)

theorem scalarCubeProductMeasure_real_apply {I α : Type*} [Fintype I] [Fintype α]
    [DecidableEq α] (s : Set (I → Option α → ℝ)) (hs : MeasurableSet s) :
    (scalarCubeProductMeasure I α).real s = scalarCubeDomainDensity α ^ Fintype.card I *
      volume.real (scalarCubeProductDomain I α ∩ s) := by
  rw [scalarCubeProductMeasure_eq_smul_restrict, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply hs, ENNReal.toReal_pow, ENNReal.toReal_inv, Set.inter_comm]
  rfl

theorem blockCubeMeasure_real_apply_domain {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α]
    (s : Set (BlockParameter B F α → ℝ)) (hs : MeasurableSet s) :
    (blockCubeMeasure B F α).real s =
      scalarCubeDomainDensity α ^ Fintype.card (B × F) * volume.real (blockCubeDomain B F α ∩ s) := by
  rw [blockCubeMeasure_real_apply s hs, scalarCubeProductMeasure_real_apply _
    (hs.preimage (blockCubeFlatten B F α).continuous.measurable)]
  have he : scalarCubeProductDomain (B × F) α ∩ blockCubeFlatten B F α ⁻¹' s =
      blockCubeFlatten B F α ⁻¹' (blockCubeDomain B F α ∩ s) := by
    ext x
    simp only [blockCubeDomain, Set.mem_inter_iff, Set.mem_preimage,
      ContinuousLinearEquiv.symm_apply_apply]
  rw [he, (blockCubeFlatten_measurePreserving B F α).measureReal_preimage
    ((blockCubeDomain_measurable B F α).inter hs).nullMeasurableSet]

end Erdos3

end

end OAI
