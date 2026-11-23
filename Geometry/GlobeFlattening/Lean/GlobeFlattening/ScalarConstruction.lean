import GlobeFlattening.SphereChart
import GlobeFlattening.SphereMesh
import GlobeFlattening.TrimmedTiles

/-!
# The scalar prescribed-gradient construction on the sphere's chart

The initial function is the affine-in-longitude sinusoidal profile with a
positive slope bonus. Each step chooses a sufficiently fine square mesh,
then lowers that bonus while keeping the trimmed affine tiles and their
quantitative error bounds.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GlobeFlattening

noncomputable section

private def sphericalCoordinateArea : ℝ := 2 * Real.pi ^ 2

private def initialScalar (δ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Real.cos p.2 + δ) * p.1

private theorem sphereLongitudeDomain_subset_box : sphereLongitudeDomain ⊆ sphereClosedBox :=
  fun _ hp => ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩

private structure ScalarStage (δ : ℝ) (n : ℕ) where
  approx : ℝ × ℝ → ℝ
  continuousOn : ContinuousOn approx sphereClosedBox
  radius : ℝ
  radius_pos : 0 < radius
  meshWidth : ℝ
  meshWidth_le : meshWidth ≤ 3 * δ / (4 : ℝ)^n
  good : Set (ℝ × ℝ)
  good_measurable : MeasurableSet good
  discarded_le : volume (sphereClosedBox \ good) ≤
    ENNReal.ofReal (if n = 0 then sphericalCoordinateArea
      else 7 * stageMargin n * sphericalCoordinateArea)
  lowerSlope : ∀ p ∈ sphereClosedBox, ∀ q ∈ sphereClosedBox, p.2 = q.2 → p.1 ≤ q.1 →
    stageTarget δ n p.2 * (q.1 - p.1) ≤ approx q - approx p
  affine_near : ∀ p ∈ good, ∃ intercept slope : ℝ, ∀ q, dist q p ≤ radius →
    approx q = intercept + slope * q.1 ∧
    stageTarget δ n q.2 ≤ slope ∧ slope ≤ stageTarget δ n q.2 + 2 * meshWidth

private def ScalarStage.tileSlope {δ : ℝ} {n : ℕ} (s : ScalarStage δ n) (p : ℝ × ℝ) : ℝ := by
  classical
  exact if hp : p ∈ s.good then (s.affine_near p hp).choose_spec.choose else 0

private theorem ScalarStage.affine_at_tileSlope {δ : ℝ} {n : ℕ} (s : ScalarStage δ n)
    {p : ℝ × ℝ} (hp : p ∈ s.good) :
    ∃ intercept : ℝ, ∀ q, dist q p ≤ s.radius →
      s.approx q = intercept + s.tileSlope p * q.1 ∧
      stageTarget δ n q.2 ≤ s.tileSlope p ∧
      s.tileSlope p ≤ stageTarget δ n q.2 + 2 * s.meshWidth := by
  refine ⟨(s.affine_near p hp).choose, ?_⟩
  simpa [ScalarStage.tileSlope, hp] using (s.affine_near p hp).choose_spec.choose_spec

private structure StageTransition {δ : ℝ} {n : ℕ}
    (before : ScalarStage δ n) (after : ScalarStage δ (n + 1)) : Prop where
  radius_le : after.radius ≤ before.radius / 2
  uniformError : ∀ q ∈ sphereClosedBox,
    |after.approx q - before.approx q| ≤ before.radius / 2 / (2 : ℝ)^n
  localError : ∀ p ∈ before.good, ∀ q ∈ sphereClosedBox, dist q p ≤ before.radius / 2 →
    |after.approx q - before.approx q| ≤ (108 * δ / (2 : ℝ)^n) * after.radius

private def zeroStage {δ : ℝ} (hδ : 0 < δ) : ScalarStage δ 0 where
  approx := initialScalar δ
  continuousOn := by unfold initialScalar; fun_prop
  radius := δ
  radius_pos := hδ
  meshWidth := 0
  meshWidth_le := by positivity
  good := ∅
  good_measurable := MeasurableSet.empty
  discarded_le := by
    rw [sdiff_empty, volume_sphereClosedBox, if_pos rfl]
    rfl
  lowerSlope := by
    intro p hp q hq hlat hlong
    unfold initialScalar
    rw [hlat, stageTarget_zero]
    apply le_of_eq
    ring
  affine_near := by simp

private theorem exists_nextStage {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (before : ScalarStage δ n) :
    ∃ after : ScalarStage δ (n + 1), StageTransition before after := by
  obtain ⟨g, hgrect, hgmargin, hgratio, hg4, hgarea, hg_gap, hg_radius, hg_half, hgosc⟩ :=
    exists_scheduledSphereMesh before.continuousOn hδ before.radius_pos n
  have newSlopeGap := stageTarget_gap hg_gap
  have holdSlope : g.HasLowerSlope before.approx (stageTarget δ n) := by
    apply g.hasLowerSlope_iff_same_latitude.mpr
    simpa only [hgrect] using before.lowerSlope
  let after : ScalarStage δ (n + 1) :=
    { approx := g.refineStage before.approx (stageTarget δ (n + 1))
      continuousOn := (g.continuous_refineStage _ _).continuousOn
      radius := g.margin
      radius_pos := g.margin_pos
      meshWidth := g.width
      meshWidth_le := hg_gap
      good := g.trimmedTiles
      good_measurable := g.isClosed_trimmedTiles.measurableSet
      discarded_le := by
        rw [← hgrect]
        simpa only [hgratio, hgarea, Nat.succ_ne_zero, if_false, sphericalCoordinateArea]
          using g.volume_discarded hg4
      lowerSlope := by
        rw [← hgrect, ← g.hasLowerSlope_iff_same_latitude]
        exact g.refineStage_lowerSlope holdSlope newSlopeGap (stageTarget_variation δ (n + 1))
      affine_near := fun _ hp => g.exists_affine_near_trimmed (stageTarget_variation δ (n + 1)) hp }
  refine ⟨after, ?_, ?_, ?_⟩
  · change g.margin ≤ before.radius / 2
    exact hg_half
  · intro q hq
    have hnonneg : ∀ y ∈ Icc g.bottom (g.latitude (g.transitions + 1)),
        0 ≤ stageTarget δ (n + 1) y := by
      intro y hy
      have hleft : g.left ∈ Icc g.left (g.longitude g.columns) := by
        simpa [RectangularMesh.longitude, meshPoint] using g.longitude_mem (Nat.zero_le _)
      have hmem : (g.left, y) ∈ sphereClosedBox := hgrect ▸ ⟨hleft, hy⟩
      exact stageTarget_nonneg δ hδ.le (n + 1) hmem.2
    have hqg : q ∈ g.rectangle := hgrect.symm ▸ hq
    have hs := g.refineStage_uniform_error holdSlope newSlopeGap hnonneg hgosc hqg
    convert hs using 1
    ring
  · intro p hp q hq hnear
    obtain ⟨a, b, haffine⟩ := before.affine_near p hp
    have htile (z : ℝ × ℝ) (hz : dist z q ≤ g.width) : dist z p ≤ before.radius := by
      have ht := (dist_triangle z q p).trans (add_le_add hz hnear)
      linarith [before.radius_pos]
    have hlocal := g.refineStage_local_error (hgrect.symm ▸ hq) newSlopeGap
      (fun y => (stageTarget_difference δ n y).le) (fun z _ hz => (haffine z (htile z hz)).1)
      (fun z _ hz => (haffine z (htile z hz)).2)
    change |g.refineStage before.approx (stageTarget δ (n + 1)) q - before.approx q| ≤
      (108 * δ / (2 : ℝ)^n) * g.margin
    refine hlocal.trans ?_
    rw [hgmargin]
    have hnormalize : stageMargin (n + 1) * g.width = g.width / (2 : ℝ) ^ (n + 4) := by
      unfold stageMargin
      ring
    rw [hnormalize]
    exact local_refinement_dyadic_bound before.meshWidth_le g.width_pos.le

private def nextStage {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (before : ScalarStage δ n) :
    ScalarStage δ (n + 1) :=
  (exists_nextStage hδ before).choose

private def scalarStages {δ : ℝ} (hδ : 0 < δ) : (n : ℕ) → ScalarStage δ n
  | 0 => zeroStage hδ
  | n + 1 => nextStage hδ (scalarStages hδ n)

private theorem scalarStages_transition {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    StageTransition (scalarStages hδ n) (scalarStages hδ (n + 1)) :=
  (exists_nextStage hδ (scalarStages hδ n)).choose_spec

/-- The scalar proposition in the report, with a specified measurable good
set and a classical Fréchet derivative at every point of that set. -/
theorem exists_scalar_flattening {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℝ × ℝ → ℝ, ∃ E : Set (ℝ × ℝ),
      ContinuousOn u sphereClosedBox ∧ MeasurableSet E ∧ E ⊆ sphereLongitudeDomain ∧
      volume (sphereLongitudeDomain \ E) = 0 ∧
      (∀ q ∈ sphereClosedBox, |u q - (Real.cos q.2 + δ) * q.1| ≤ δ) ∧
      (∀ p ∈ sphereClosedBox, ∀ q ∈ sphereClosedBox, p.2 = q.2 → p.1 ≤ q.1 →
        Real.cos p.2 * (q.1 - p.1) ≤ u q - u p) ∧
      ∀ p ∈ E, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  let s := scalarStages hδ
  have hbad : (∑' n, volume (sphereLongitudeDomain \ (s n).good)) ≠ ∞ := by
    have hcompare (n : ℕ) :
        volume (sphereLongitudeDomain \ (s n).good) ≤ volume (sphereClosedBox \ (s n).good) :=
      measure_mono (sdiff_subset_sdiff_left sphereLongitudeDomain_subset_box)
    apply sphereMesh_bad_area_summable
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((hcompare 0).trans (s 0).discarded_le)
    · intro n
      simpa only [Nat.succ_ne_zero, if_false, sphericalCoordinateArea] using
        (hcompare (n + 1)).trans (s (n + 1)).discarded_le
  refine exists_scalar_limit_of_refinement_stages isOpen_sphereLongitudeDomain
    sphereLongitudeDomain_subset_box
    (approx := fun n => (s n).approx) (good := fun n => (s n).good)
    (radius := fun n => (s n).radius) (stageSlope := stageTarget δ)
    (tileSlope := fun n => (s n).tileSlope) (slopeError := fun n => 7 * δ / (4 : ℝ)^n)
    (localCoeff := fun n => 108 * δ / (2 : ℝ)^n)
    (fun n => (s n).radius_pos) (fun n => (scalarStages_transition hδ n).radius_le)
    (fun n => (s n).continuousOn) (fun n => (scalarStages_transition hδ n).uniformError)
    (fun n => (s n).good_measurable) hbad (stageTarget_tendsto δ)
    (fun n => (s n).lowerSlope) (tendsto_quarter_ratio_zero _) (tendsto_dyadic_ratio_zero _) ?_ ?_
  · intro n p hp _
    obtain ⟨_, htile⟩ := (s n).affine_at_tileSlope hp
    have hb := (htile p (by simpa using (s n).radius_pos.le)).2
    unfold stageTarget at hb
    have hwidth := (s n).meshWidth_le
    rw [mul_div_assoc] at hwidth
    have hnonneg : 0 ≤ δ / (4 : ℝ)^n := by positivity
    rw [mul_div_assoc]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith only [hb.1, hnonneg]
    · linarith only [hb.2, hwidth]
  · intro n p hp _ q hq hdist
    have hnear : dist q p ≤ (s n).radius / 2 := by
      simpa [dist_eq_norm] using hdist.le
    obtain ⟨intercept, htile⟩ := (s n).affine_at_tileSlope hp
    have hpval := (htile p (by simpa using (s n).radius_pos.le)).1
    have hqval := (htile q (hnear.trans (by linarith [(s n).radius_pos]))).1
    refine ⟨?_, (scalarStages_transition hδ n).localError p hp q
      (sphereLongitudeDomain_subset_box hq) hnear⟩
    rw [hpval, hqval]
    ring


end

end GlobeFlattening
