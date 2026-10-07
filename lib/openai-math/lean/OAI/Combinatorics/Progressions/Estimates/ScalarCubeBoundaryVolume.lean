import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberVolumeBound
import OAI.Combinatorics.Progressions.Geometry.ScalarCubeCoordinates

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def scalarCubeFaceStrip {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) : Set (Option α → ℝ) :=
  scalarCubeDomain α ∩ {a | scalarCubeFace i a < u}

theorem scalarCubeFaceStrip_measurable {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) : MeasurableSet (scalarCubeFaceStrip i u) :=
  (scalarCubeDomain_isOpen α).measurableSet.inter
    (measurableSet_lt (scalarCubeFace_contDiff i).continuous.measurable measurable_const)

theorem scalarCubeFaceStrip_volume_lt_top {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) : volume (scalarCubeFaceStrip i u) < ⊤ :=
  (measure_mono Set.inter_subset_left).trans_lt (scalarCubeDomain_volume_lt_top α)

theorem scalarCubeFaceStrip_fiber_interval {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) (b : α → ℝ) :
    ∃ lo : ℝ, {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceStrip i u} ⊆ Set.Ioo lo (lo + u) := by
  rcases i with ⟨side, t⟩
  cases side with
  | false =>
    refine ⟨-(∑ k ∈ t, b k), ?_⟩
    intro y hy
    have hpos := (hy.1 t).1
    have hupper := hy.2
    change scalarCubeValue (scalarCubeJoin (b, y)) t < u at hupper
    rw [scalarCubeJoin_value] at hpos hupper
    exact ⟨by linarith, by linarith⟩
  | true =>
    refine ⟨1 - (∑ k ∈ t, b k) - u, ?_⟩
    intro y hy
    have hpos := (hy.1 t).2
    have hlower := hy.2
    change 1 - scalarCubeValue (scalarCubeJoin (b, y)) t < u at hlower
    rw [scalarCubeJoin_value] at hpos hlower
    exact ⟨by linarith, by linarith⟩

theorem scalarCubeFaceStrip_fiber_volume_le {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) {u : ℝ} (hu : 0 ≤ u) (b : α → ℝ) :
    volume.real {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceStrip i u} ≤ u := by
  obtain ⟨lo, hsub⟩ := scalarCubeFaceStrip_fiber_interval i u b
  have hlen : volume.real (Set.Ioo lo (lo + u)) = u := by
    rw [Real.volume_real_Ioo]
    simpa only [add_sub_cancel_left] using max_eq_left hu
  exact (measureReal_mono (μ := volume) hsub (by simp [Real.volume_Ioo])).trans_eq hlen

theorem scalarCubeFaceStrip_base_bound {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (u : ℝ) {z : (α → ℝ) × ℝ}
    (hz : scalarCubeJoin z ∈ scalarCubeFaceStrip i u) : z.1 ∈ Metric.closedBall (0 : α → ℝ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro k
  have h := (scalarCubeDomain_coordinate_abs_lt_one hz.1 (some k)).le
  simpa only [scalarCubeJoin_some, Real.norm_eq_abs] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeFaceStrip_volume_le {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) {u : ℝ} (hu : 0 ≤ u) :
    volume.real (scalarCubeFaceStrip i u) ≤ (2 : ℝ) ^ Fintype.card α * u := by
  let s : Set ((α → ℝ) × ℝ) := scalarCubeJoin ⁻¹' scalarCubeFaceStrip i u
  have hs : MeasurableSet s := (scalarCubeFaceStrip_measurable i u).preimage (scalarCubeJoin_measurable α)
  have hpres := scalarCubeJoin_measurePreserving α
  have hmass : volume s = volume (scalarCubeFaceStrip i u) :=
    hpres.measure_preimage (scalarCubeFaceStrip_measurable i u).nullMeasurableSet
  have hreal : volume.real s = volume.real (scalarCubeFaceStrip i u) :=
    hpres.measureReal_preimage (scalarCubeFaceStrip_measurable i u).nullMeasurableSet
  have hsfin : (volume : Measure ((α → ℝ) × ℝ)) s ≠ ⊤ := by
    rw [hmass]
    exact (scalarCubeFaceStrip_volume_lt_top i u).ne
  have h := product_measureReal_le_of_fiber_bound
    (volume : Measure (α → ℝ)) (volume : Measure ℝ) s hs hsfin
    (Metric.closedBall (0 : α → ℝ) 1) measurableSet_closedBall
    (isCompact_closedBall _ _).measure_ne_top
    (fun z hz => scalarCubeFaceStrip_base_bound i u hz)
    (scalarCubeFaceStrip_fiber_volume_le i hu)
  change volume.real s ≤ _ at h
  rw [hreal] at h
  have hbase : volume.real (Metric.closedBall (0 : α → ℝ) 1) = (2 : ℝ) ^ Fintype.card α := by
    rw [measureReal_def, Real.volume_pi_closedBall _ (by norm_num)]
    simp
  rw [hbase] at h
  exact h

theorem scalarCubeFaceStrip_weighted_volume_le {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) {u : ℝ} (hu : 0 ≤ u) :
    (∫ _ in scalarCubeFaceStrip i u, scalarCubeDomainDensity α) ≤
      scalarCubeDomainDensity α * (2 : ℝ) ^ Fintype.card α * u := by
  rw [setIntegral_const, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (scalarCubeFaceStrip_volume_le i hu)
    (scalarCubeDomainDensity_pos α).le
  nlinarith

end Erdos3

end

end OAI
