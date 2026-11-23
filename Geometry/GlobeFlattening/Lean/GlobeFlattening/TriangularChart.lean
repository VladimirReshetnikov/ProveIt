import GlobeFlattening.CoordinateRectangles
import GlobeFlattening.RestrictedArea

/-!
# The triangular flattening chart

Continuity and strict increase on each row make the closed rectangle
embed by compactness. The interior maps onto the open chart image.
-/

open Filter Set Topology
open scoped Topology

namespace GlobeFlattening

/-- The region between the left and right endpoint profiles. -/
def chartImage (u : ℝ × ℝ → ℝ) (a b c d : ℝ) : Set (ℝ × ℝ) :=
  Prod.swap ⁻¹' regionBetween (fun y => u (a, y)) (fun y => u (b, y)) (Ioo c d)

/-- Every neighborhood contains a closed rectangle with the point in its interior. -/
theorem exists_chartClosedRectangle_subset_of_mem_nhds {p : ℝ × ℝ} {W : Set (ℝ × ℝ)}
    (hW : W ∈ 𝓝 p) :
    ∃ a b c d : ℝ, p ∈ chartRectangle a b c d ∧ chartClosedRectangle a b c d ⊆ W := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hW
  refine ⟨p.1 - r, p.1 + r, p.2 - r, p.2 + r, ?_, ?_⟩
  · exact ⟨⟨sub_lt_self _ hr, lt_add_of_pos_right _ hr⟩, ⟨sub_lt_self _ hr, lt_add_of_pos_right _ hr⟩⟩
  · simpa only [chartClosedRectangle, ← Real.closedBall_eq_Icc, closedBall_prod_same] using hsub

theorem continuousOn_latitudeProfile {u : ℝ × ℝ → ℝ} {a b c d x : ℝ}
    (hu : ContinuousOn u (chartClosedRectangle a b c d)) (hx : x ∈ Icc a b) :
    ContinuousOn (fun y => u (x, y)) (Icc c d) :=
  ContinuousOn.uncurry_left (f := fun x y => u (x, y)) x hx hu

theorem isOpen_chartImage {u : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (chartClosedRectangle a b c d)) :
    IsOpen (chartImage u a b c d) := by
  let latitudeStrip := (Prod.snd : ℝ × ℝ → ℝ) ⁻¹' Ioo c d
  have hprofile (x : ℝ) (hx : x ∈ Icc a b) :
      ContinuousOn (fun p : ℝ × ℝ => u (x, p.2)) latitudeStrip :=
    (continuousOn_latitudeProfile hu hx).comp' continuous_snd.continuousOn
      (fun _ hp => Ioo_subset_Icc_self hp)
  have hlower := (hprofile a ⟨le_rfl, hab⟩).prodMk continuous_fst.continuousOn
  have hupper := continuous_fst.continuousOn.prodMk (hprofile b ⟨hab, le_rfl⟩)
  exact (hlower.prodMk hupper).isOpen_inter_preimage
    (isOpen_Ioo.preimage continuous_snd) (isOpen_lt_prod.prod isOpen_lt_prod)

/-- A strict lower slope bound with a nonnegative slope gives increasing longitude rows. -/
theorem strictMonoOn_chartRows_of_lowerSlope {u : ℝ × ℝ → ℝ} {slope : ℝ → ℝ} {a b c d : ℝ}
    (hnonneg : ∀ y ∈ Icc c d, 0 ≤ slope y)
    (hslope : ∀ p ∈ chartClosedRectangle a b c d, ∀ q ∈ chartClosedRectangle a b c d,
      p.2 = q.2 → p.1 < q.1 → slope p.2 * (q.1 - p.1) < u q - u p) :
    ∀ y ∈ Icc c d, StrictMonoOn (fun x => u (x, y)) (Icc a b) := by
  intro y hy x hx z hz hxz
  exact sub_pos.mp ((mul_nonneg (hnonneg y hy) (sub_nonneg.mpr hxz.le)).trans_lt
    (hslope (x, y) ⟨hx, hy⟩ (z, y) ⟨hz, hy⟩ rfl hxz))

theorem injOn_flattenCoordinates_closedRectangle {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hmono : ∀ y ∈ Icc c d, StrictMonoOn (fun x => u (x, y)) (Icc a b)) :
    InjOn (flattenCoordinates u) (chartClosedRectangle a b c d) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨z, w⟩ ⟨hz, _⟩ heq
  obtain ⟨hu, rfl⟩ := Prod.mk.inj heq
  exact Prod.ext ((hmono y hy).injOn hx hz hu) rfl

theorem image_flattenCoordinates_chartRectangle {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b)) :
    flattenCoordinates u '' chartRectangle a b c d = chartImage u a b c d := by
  have hrow (y : ℝ) (hy : y ∈ Ioo c d) :=
    ContinuousOn.image_Ioo_of_strictMonoOn hab
      (ContinuousOn.uncurry_right (f := fun x y => u (x, y)) y (Ioo_subset_Icc_self hy) hu) (hmono y hy)
  ext ⟨x, y⟩
  change (∃ p ∈ Ioo a b ×ˢ Ioo c d, (u p, p.2) = (x, y)) ↔
    y ∈ Ioo c d ∧ x ∈ Ioo (u (a, y)) (u (b, y))
  grind [Prod.exists]

/-- The closed rectangle embeds by compactness. Its interior maps onto the
open region between the endpoint profiles. -/
@[simps! source target apply]
noncomputable def triangularChart {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Icc c d, StrictMonoOn (fun x => u (x, y)) (Icc a b)) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := by
  let s := chartRectangle a b c d
  let box := chartClosedRectangle a b c d
  have hcont : ContinuousOn (flattenCoordinates u) box := hu.prodMk continuous_snd.continuousOn
  have hinj := injOn_flattenCoordinates_closedRectangle hmono
  letI : CompactSpace box := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  have he : IsEmbedding (s.restrict (flattenCoordinates u)) :=
    (hcont.restrict.isClosedEmbedding hinj.injective).isEmbedding.comp
      (IsEmbedding.inclusion chartRectangle_subset_closed)
  have hbij : BijOn (flattenCoordinates u) s (chartImage u a b c d) :=
    image_flattenCoordinates_chartRectangle hab hu (fun y hy => hmono y (Ioo_subset_Icc_self hy)) ▸
      (hinj.mono chartRectangle_subset_closed).bijOn_image
  exact OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hbij.toPartialEquiv (flattenCoordinates u) s _) (hcont.mono chartRectangle_subset_closed)
    (he.isInducing.isOpenMap (by
      simpa only [range_restrict, hbij.image_eq] using isOpen_chartImage hab hu))
    (isOpen_chartRectangle _ _ _ _)

end GlobeFlattening
