/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.NormalizedRestrictionTransport
import OAI.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass

namespace OAI

section

namespace Erdos3

open MeasureTheory

def closedScalarCubeDomain (α : Type*) [Fintype α] [DecidableEq α] : Set (Option α → ℝ) :=
  {a | ∀ t : Finset α, scalarCubeValue a t ∈ Set.Icc (0 : ℝ) 1}

theorem scalarCubeDomain_subset_closed (α : Type*) [Fintype α] [DecidableEq α] :
    scalarCubeDomain α ⊆ closedScalarCubeDomain α :=
  fun _ ha t => ⟨(ha t).1.le, (ha t).2.le⟩

theorem closedScalarCubeDomain_isClosed (α : Type*) [Fintype α] [DecidableEq α] :
    IsClosed (closedScalarCubeDomain α) := by
  have heq : closedScalarCubeDomain α = ⋂ t : Finset α, {a | scalarCubeValue a t ∈ Set.Icc (0 : ℝ) 1} := by
    ext a
    simp [closedScalarCubeDomain]
  rw [heq]
  exact isClosed_iInter (fun t => isClosed_Icc.preimage (scalarCubeValue_contDiff t).continuous)

theorem closedScalarCubeDomain_iff_faces {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) : a ∈ closedScalarCubeDomain α ↔ ∀ i, 0 ≤ scalarCubeFace i a := by
  constructor
  · intro ha i
    rcases i with ⟨side, t⟩
    cases side with
    | false => exact (ha t).1
    | true => exact sub_nonneg.mpr (ha t).2
  · intro ha t
    have hlo : 0 ≤ scalarCubeValue a t := ha (false, t)
    have hhi : 0 ≤ 1 - scalarCubeValue a t := ha (true, t)
    exact ⟨hlo, by linarith⟩

theorem closedScalarCubeDomain_coordinate_abs_le_one {α : Type*} [Fintype α] [DecidableEq α]
    {a : Option α → ℝ} (ha : a ∈ closedScalarCubeDomain α) (r : Option α) : |a r| ≤ 1 := by
  have hzero := ha ∅
  rw [scalarCubeValue_empty] at hzero
  cases r with
  | none => exact abs_le.mpr ⟨by linarith [hzero.1], hzero.2⟩
  | some i =>
    have hi := ha {i}
    rw [scalarCubeValue_singleton] at hi
    exact abs_le.mpr ⟨by linarith [hzero.2, hi.1], by linarith [hzero.1, hi.2]⟩

theorem closedScalarCubeDomain_compact (α : Type*) [Fintype α] [DecidableEq α] :
    IsCompact (closedScalarCubeDomain α) := by
  apply Metric.isCompact_of_isClosed_isBounded (closedScalarCubeDomain_isClosed α)
  apply (Metric.isBounded_closedBall (x := (0 : Option α → ℝ)) (r := 1)).subset
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro r
  simpa only [Real.norm_eq_abs] using closedScalarCubeDomain_coordinate_abs_le_one ha r

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem closedScalarCubeFace_zero_volume {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) :
    volume (closedScalarCubeDomain α ∩ {a | scalarCubeFace i a = 0}) = 0 := by
  let Z := closedScalarCubeDomain α ∩ {a | scalarCubeFace i a = 0}
  have hZm : MeasurableSet Z := (closedScalarCubeDomain_isClosed α).measurableSet.inter
    (measurableSet_eq_fun (scalarCubeFace_contDiff i).continuous.measurable measurable_const)
  have hZfin : volume Z ≠ ⊤ := ne_of_lt ((measure_mono Set.inter_subset_left).trans_lt
    (closedScalarCubeDomain_compact α).measure_lt_top)
  let s : Set ((α → ℝ) × ℝ) := scalarCubeJoin ⁻¹' Z
  have hs : MeasurableSet s := hZm.preimage (scalarCubeJoin_measurable α)
  have hm := (scalarCubeJoin_measurePreserving α).measure_preimage hZm.nullMeasurableSet
  have hmr := (scalarCubeJoin_measurePreserving α).measureReal_preimage hZm.nullMeasurableSet
  have hsfin : (volume : Measure ((α → ℝ) × ℝ)) s ≠ ⊤ := by
    change volume (scalarCubeJoin ⁻¹' Z) ≠ ⊤
    rw [hm]
    exact hZfin
  have hbase : ∀ z ∈ s, z.1 ∈ Metric.closedBall (0 : α → ℝ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    have h := closedScalarCubeDomain_coordinate_abs_le_one hz.1 (some k)
    simpa only [Real.norm_eq_abs, scalarCubeJoin_some] using h
  have hbound : ∀ b : α → ℝ, volume.real {y | (b, y) ∈ s} ≤ 0 := by
    intro b
    let c : ℝ := if i.1 then 1 - ∑ k ∈ i.2, b k else -(∑ k ∈ i.2, b k)
    have hsub : {y | (b, y) ∈ s} ⊆ {c} := by
      intro y hy
      have heq : scalarCubeFace i (scalarCubeJoin (b, y)) = 0 := hy.2
      rw [scalarCubeJoin_face] at heq
      apply Set.mem_singleton_iff.mpr
      dsimp [c]
      split_ifs at heq ⊢ <;> linarith
    have h := measureReal_mono (μ := volume) hsub (by simp)
    simpa [measureReal_def] using h
  have h := product_measureReal_le_of_fiber_bound
    (volume : Measure (α → ℝ)) (volume : Measure ℝ) s hs hsfin
    (Metric.closedBall (0 : α → ℝ) 1) measurableSet_closedBall
    (isCompact_closedBall _ _).measure_ne_top hbase hbound
  change volume.real s ≤ _ at h
  rw [hmr, mul_zero] at h
  exact (measureReal_eq_zero_iff hZfin).mp (le_antisymm h measureReal_nonneg)

theorem closedScalarCubeDomain_boundary_null (α : Type*) [Fintype α] [DecidableEq α] :
    volume (closedScalarCubeDomain α \ scalarCubeDomain α) = 0 := by
  have hsub : closedScalarCubeDomain α \ scalarCubeDomain α ⊆
      ⋃ i : Bool × Finset α, closedScalarCubeDomain α ∩ {a | scalarCubeFace i a = 0} := by
    intro a ha
    have hn : ¬ ∀ i, 0 < scalarCubeFace i a := by
      intro hp
      apply ha.2
      rw [← positiveInequalityDomain_scalarCubeFace α]
      exact hp
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hz : scalarCubeFace i a = 0 := le_antisymm (le_of_not_gt hi)
      ((closedScalarCubeDomain_iff_faces a).mp ha.1 i)
    exact Set.mem_iUnion.mpr ⟨i, ha.1, hz⟩
  exact measure_mono_null hsub (measure_iUnion_null closedScalarCubeFace_zero_volume)

theorem scalarCubeDomain_ae_closed (α : Type*) [Fintype α] [DecidableEq α] :
    scalarCubeDomain α =ᵐ[volume] closedScalarCubeDomain α := by
  apply ae_eq_set.mpr
  constructor
  · have he : scalarCubeDomain α \ closedScalarCubeDomain α = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact ha.2 (scalarCubeDomain_subset_closed α ha.1)
    rw [he, measure_empty]
  · exact closedScalarCubeDomain_boundary_null α

noncomputable def closedScalarCubeMeasure (α : Type*) [Fintype α] [DecidableEq α] :
    Measure (Option α → ℝ) :=
  (volume (closedScalarCubeDomain α))⁻¹ • volume.restrict (closedScalarCubeDomain α)

theorem closedScalarCubeMeasure_eq (α : Type*) [Fintype α] [DecidableEq α] :
    closedScalarCubeMeasure α = scalarCubeMeasure α := by
  have hvol := measure_congr (scalarCubeDomain_ae_closed α)
  have hrestrict := Measure.restrict_congr_set (scalarCubeDomain_ae_closed α)
  simp only [closedScalarCubeMeasure, scalarCubeMeasure, ← hvol, ← hrestrict]

instance closedScalarCubeMeasure_probability (α : Type*) [Fintype α] [DecidableEq α] :
    IsProbabilityMeasure (closedScalarCubeMeasure α) := by
  rw [closedScalarCubeMeasure_eq]
  infer_instance

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

def halfOpenScalarCubeDomain (I : Type*) [Fintype I] [DecidableEq I] : Set (Option I → ℝ) :=
  {x | ∀ t : Finset I, scalarCubeValue x t ∈ Set.Ico (0 : ℝ) 1}

theorem halfOpenScalarCubeDomain_measurable (I : Type*) [Fintype I] [DecidableEq I] :
    MeasurableSet (halfOpenScalarCubeDomain I) := by
  have he : halfOpenScalarCubeDomain I = ⋂ t : Finset I,
      (fun x => scalarCubeValue x t) ⁻¹' Set.Ico (0 : ℝ) 1 := by
    ext x
    simp only [halfOpenScalarCubeDomain, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [he]
  exact MeasurableSet.iInter (fun (t : Finset I) =>
    measurableSet_Ico.preimage (scalarCubeValue_contDiff t).continuous.measurable)

theorem scalarCubeDomain_subset_halfOpen (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomain I ⊆ halfOpenScalarCubeDomain I :=
  fun _ hx t => ⟨(hx t).1.le, (hx t).2⟩

theorem halfOpenScalarCubeDomain_subset_closed (I : Type*) [Fintype I] [DecidableEq I] :
    halfOpenScalarCubeDomain I ⊆ closedScalarCubeDomain I :=
  fun _ hx t => ⟨(hx t).1, (hx t).2.le⟩

theorem halfOpenScalarCubeDomain_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    {x : Option I → ℝ} (hx : x ∈ halfOpenScalarCubeDomain I) : ‖x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  exact closedScalarCubeDomain_coordinate_abs_le_one (halfOpenScalarCubeDomain_subset_closed I hx) i

theorem halfOpenScalarCubeDomain_ae (I : Type*) [Fintype I] [DecidableEq I] :
    halfOpenScalarCubeDomain I =ᵐ[volume] scalarCubeDomain I := by
  filter_upwards [scalarCubeDomain_ae_closed I] with x hx
  apply propext
  have hx' : x ∈ scalarCubeDomain I ↔ x ∈ closedScalarCubeDomain I := iff_of_eq hx
  constructor
  · intro h
    exact hx'.mpr (halfOpenScalarCubeDomain_subset_closed I h)
  · exact fun h => scalarCubeDomain_subset_halfOpen I h

noncomputable def scalarCubeIndicator (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) : ℝ := if x ∈ halfOpenScalarCubeDomain I then 1 else 0

theorem scalarCubeIndicator_range (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) : 0 ≤ scalarCubeIndicator I x ∧ scalarCubeIndicator I x ≤ 1 := by
  unfold scalarCubeIndicator
  split_ifs <;> norm_num

theorem scalarCubeIndicator_zero_outside (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) (hx : 1 < ‖x‖) : scalarCubeIndicator I x = 0 := by
  apply ite_eq_right
  exact fun h => (not_lt_of_ge (halfOpenScalarCubeDomain_norm_le h)) hx

theorem scalarCubeIndicator_integrable (I : Type*) [Fintype I] [DecidableEq I] :
    Integrable (scalarCubeIndicator I) := by
  change Integrable ((halfOpenScalarCubeDomain I).indicator (fun _ => (1 : ℝ)))
  exact (integrableOn_const ((measure_mono (halfOpenScalarCubeDomain_subset_closed I)).trans_lt
    (closedScalarCubeDomain_compact I).measure_lt_top).ne).integrable_indicator
    (halfOpenScalarCubeDomain_measurable I)

theorem scalarCubeIndicator_integral (I : Type*) [Fintype I] [DecidableEq I] :
    (∫ x, scalarCubeIndicator I x) = volume.real (scalarCubeDomain I) := by
  have he : scalarCubeIndicator I =ᵐ[volume] (scalarCubeDomain I).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [halfOpenScalarCubeDomain_ae I] with x hx
    have hx' : (x ∈ halfOpenScalarCubeDomain I) = (x ∈ scalarCubeDomain I) := hx
    change (if x ∈ halfOpenScalarCubeDomain I then 1 else 0) =
      if x ∈ scalarCubeDomain I then 1 else 0
    rw [hx']
  rw [integral_congr_ae he]
  exact integral_indicator_one (scalarCubeDomain_isOpen I).measurableSet

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeValue_smul {α : Type*} [Fintype α] [DecidableEq α]
    (T : ℝ) (a : Option α → ℝ) (vertex : Finset α) :
    scalarCubeValue (T • a) vertex = T * scalarCubeValue a vertex := by
  simp only [scalarCubeValue, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

def scaledScalarCubeDomain (α : Type*) [Fintype α] [DecidableEq α] (T : ℝ) :
    Set (Option α → ℝ) :=
  {a | ∀ vertex : Finset α, scalarCubeValue a vertex ∈ Set.Ioo (0 : ℝ) T}

theorem scaledScalarCubeDomain_smul_iff {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) (a : Option α → ℝ) :
    T • a ∈ scaledScalarCubeDomain α T ↔ a ∈ scalarCubeDomain α := by
  change (∀ vertex, 0 < scalarCubeValue (T • a) vertex ∧ scalarCubeValue (T • a) vertex < T) ↔ _
  simp only [scalarCubeValue_smul, mul_pos_iff_of_pos_left hT,
    mul_lt_iff_lt_one_right hT]
  rfl

theorem scaledScalarCubeDomain_eq_image {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) :
    scaledScalarCubeDomain α T = (T • ·) '' scalarCubeDomain α := by
  ext a
  constructor
  · intro ha
    refine ⟨T⁻¹ • a, ?_, smul_inv_smul₀ hT.ne' a⟩
    apply (scaledScalarCubeDomain_smul_iff hT _).mp
    simpa only [smul_inv_smul₀ hT.ne'] using ha
  · rintro ⟨a, ha, rfl⟩
    exact (scaledScalarCubeDomain_smul_iff hT a).mpr ha

theorem scaledScalarCubeDomain_isOpen (α : Type*) [Fintype α] [DecidableEq α]
    (T : ℝ) : IsOpen (scaledScalarCubeDomain α T) := by
  have he : scaledScalarCubeDomain α T =
      ⋂ vertex : Finset α, (scalarCubeValue · vertex) ⁻¹' Set.Ioo (0 : ℝ) T := by
    ext a
    simp [scaledScalarCubeDomain]
  rw [he]
  exact isOpen_iInter_of_finite (fun vertex =>
    isOpen_Ioo.preimage (scalarCubeValue_contDiff vertex).continuous)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def scalarCubeFaceSlab {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) (u : ℝ) : Set (Option I → ℝ) :=
  Metric.closedBall 0 2 ∩ {x | |scalarCubeFace i x| ≤ u}

theorem scalarCubeFaceSlab_measurable {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) (u : ℝ) : MeasurableSet (scalarCubeFaceSlab i u) :=
  measurableSet_closedBall.inter (measurableSet_le
    (scalarCubeFace_contDiff i).continuous.abs.measurable measurable_const)

theorem scalarCubeFaceSlab_finite {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) (u : ℝ) : volume (scalarCubeFaceSlab i u) ≠ ⊤ :=
  ne_of_lt ((measure_mono Set.inter_subset_left).trans_lt (isCompact_closedBall _ _).measure_lt_top)

theorem scalarCubeFaceSlab_fiber_bound {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) {u : ℝ} (hu : 0 ≤ u) (b : I → ℝ) :
    volume.real {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceSlab i u} ≤ 2*u := by
  let c : ℝ := if i.1 then 1 - ∑ k ∈ i.2, b k else -(∑ k ∈ i.2, b k)
  have hsub : {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceSlab i u} ⊆ Set.Icc (c-u) (c+u) := by
    intro y hy
    have hraw : |scalarCubeFace i (scalarCubeJoin (b,y))| ≤ u := hy.2
    have h := abs_le.mp hraw
    rw [scalarCubeJoin_face] at h
    dsimp only [c]
    split_ifs at h ⊢ <;> constructor <;> linarith
  have hv : volume.real (Set.Icc (c-u) (c+u)) = 2*u := by
    rw [Real.volume_real_Icc]
    simp only [show c+u-(c-u) = 2*u by ring, max_eq_left (by positivity : 0 ≤ 2*u)]
  exact (measureReal_mono (μ := volume) hsub (by simp [Real.volume_Icc])).trans_eq hv

theorem scalarCubeFaceSlab_volume_le {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) {u : ℝ} (hu : 0 ≤ u) :
    volume.real (scalarCubeFaceSlab i u) ≤ (4 : ℝ)^Fintype.card I * (2*u) := by
  let s := scalarCubeJoin ⁻¹' scalarCubeFaceSlab i u
  have hs : MeasurableSet s := (scalarCubeFaceSlab_measurable i u).preimage (scalarCubeJoin_measurable I)
  have hm := (scalarCubeJoin_measurePreserving I).measure_preimage (scalarCubeFaceSlab_measurable i u).nullMeasurableSet
  have hmr := (scalarCubeJoin_measurePreserving I).measureReal_preimage (scalarCubeFaceSlab_measurable i u).nullMeasurableSet
  have hfin : (volume : Measure ((I → ℝ) × ℝ)) s ≠ ⊤ := by
    change volume (scalarCubeJoin ⁻¹' scalarCubeFaceSlab i u) ≠ ⊤
    rw [hm]
    exact scalarCubeFaceSlab_finite i u
  have hb : ∀ z ∈ s, z.1 ∈ Metric.closedBall (0 : I → ℝ) 2 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro k
    have hh : ‖scalarCubeJoin z‖ ≤ 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
    exact (norm_le_pi_norm (scalarCubeJoin z) (some k)).trans hh
  have h := product_measureReal_le_of_fiber_bound
    (volume : Measure (I → ℝ)) (volume : Measure ℝ) s hs hfin
    (Metric.closedBall (0 : I → ℝ) 2) measurableSet_closedBall (isCompact_closedBall _ _).measure_ne_top
    hb (scalarCubeFaceSlab_fiber_bound i hu)
  change volume.real s ≤ _ at h
  rw [hmr] at h
  have hbase : volume.real (Metric.closedBall (0 : I → ℝ) 2) = (4 : ℝ)^Fintype.card I := by
    rw [measureReal_def, Real.volume_pi_closedBall _ (by norm_num)]
    norm_num
  rwa [hbase] at h

end Erdos3

end

end OAI
