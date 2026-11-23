import GlobeFlattening.CoordinateArea

/-!
# Strict local excess in the flattening chart

The strict longitude slope gives excess width at every latitude.
Comparing the area formulas isolates the exceptional image.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace GlobeFlattening

/-- On every open rectangle with closure inside the cut-sphere chart,
the exceptional image has positive planar measure. -/
theorem volume_local_exceptional_image_pos {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hbox : chartClosedRectangle a b c d ⊆ sphereLongitudeDomain)
    (hu : ContinuousOn u sphereClosedBox)
    (hslope : ∀ p ∈ sphereClosedBox, ∀ q ∈ sphereClosedBox,
      p.2 = q.2 → p.1 < q.1 → Real.cos p.2 * (q.1 - p.1) < u q - u p)
    (hgood : MeasurableSet good) (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p) :
    0 < volume (flattenCoordinates u '' (chartRectangle a b c d \ good)) := by
  let R := chartRectangle a b c d
  have hR : IsOpen R := isOpen_chartRectangle _ _ _ _
  have hsub := hbox.trans sphereLongitudeDomain_subset_box
  have hRsub := chartRectangle_subset_closed.trans hbox
  have hRectNull : volume (R \ good) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left hRsub) hnull
  have hcos : ∀ y ∈ Icc c d, 0 ≤ Real.cos y := by
    intro y hy
    have hp : (a, y) ∈ chartClosedRectangle a b c d :=
      ⟨⟨le_rfl, hab.le⟩, hy⟩
    exact (Real.cos_pos_of_mem_Ioo (hbox hp).2).le
  have hslope' (p) (hp) (q) (hq) := hslope p (hsub hp) q (hsub hq)
  have hmono := strictMonoOn_chartRows_of_lowerSlope hcos hslope'
  let g := triangularChart hab.le (hu.mono hsub) hmono
  have hinj : InjOn (flattenCoordinates u) R := g.injOn
  have himage : flattenCoordinates u '' R = chartImage u a b c d := g.image_source_eq_target
  have hAreaLt : volume (flattenCoordinates u '' (R ∩ good)) <
      volume (flattenCoordinates u '' R) := by
    rw [measure_flattened_good_image (hR.measurableSet.inter hgood) inter_subset_left
        (by rwa [sdiff_self_inter]) hinj
        (fun p hp => (hderiv p hp.2).hasFDerivWithinAt)
        (fun p hp => hcos p.2 (Ioo_subset_Icc_self hp.1.2)), himage]
    exact lintegral_cos_lt_volume_chartImage hab hcd (hu.mono hsub)
      (fun y hy => hcos y (Ioo_subset_Icc_self hy)) hslope'
  refine pos_iff_ne_zero.2 fun hazero => hAreaLt.not_ge ?_
  have hsplit := measure_union_le (μ := volume) (flattenCoordinates u '' (R ∩ good))
    (flattenCoordinates u '' (R \ good))
  rw [← image_union, inter_union_sdiff, hazero, add_zero] at hsplit
  exact hsplit

/-- Every nonempty open subset of the planar image meets the exceptional
image in a set of positive area. -/
theorem volume_exceptional_inter_of_open {u : ℝ × ℝ → ℝ} {good W : Set (ℝ × ℝ)}
    (hu : ContinuousOn u sphereClosedBox)
    (hslope : ∀ p ∈ sphereClosedBox, ∀ q ∈ sphereClosedBox,
      p.2 = q.2 → p.1 < q.1 → Real.cos p.2 * (q.1 - p.1) < u q - u p)
    (hgood : MeasurableSet good) (hnull : volume (sphereLongitudeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p)
    (hW : IsOpen W) (hne : W.Nonempty) (hWsub : W ⊆ flattenCoordinates u '' sphereLongitudeDomain) :
    0 < volume (W ∩ flattenCoordinates u '' (sphereLongitudeDomain \ good)) := by
  let V := sphereLongitudeDomain ∩ flattenCoordinates u ⁻¹' W
  have hcont : ContinuousOn (flattenCoordinates u) sphereLongitudeDomain :=
    (hu.mono sphereLongitudeDomain_subset_box).prodMk continuous_snd.continuousOn
  have hV : IsOpen V := hcont.isOpen_inter_preimage isOpen_sphereLongitudeDomain hW
  obtain ⟨q, hq⟩ := hne
  obtain ⟨p, hp, rfl⟩ := hWsub hq
  have hpV : p ∈ V := ⟨hp, hq⟩
  obtain ⟨a, b, c, d, hp', hsub⟩ := exists_chartClosedRectangle_subset_of_mem_nhds (hV.mem_nhds hpV)
  have hbox : chartClosedRectangle a b c d ⊆ sphereLongitudeDomain := hsub.trans inter_subset_left
  refine (volume_local_exceptional_image_pos (hp'.1.1.trans hp'.1.2) (hp'.2.1.trans hp'.2.2)
    hbox hu hslope hgood hnull hderiv).trans_le (measure_mono ?_)
  rintro _ ⟨p, hp, rfl⟩
  have hpV := hsub (chartRectangle_subset_closed hp.1)
  exact ⟨hpV.2, ⟨p, ⟨hpV.1, hp.2⟩, rfl⟩⟩

end GlobeFlattening
