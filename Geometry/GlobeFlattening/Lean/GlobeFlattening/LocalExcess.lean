import GlobeFlattening.CoordinateArea

/-!
# Strict local excess in the flattening chart

The strict longitude slope gives excess width at every latitude.
Comparing the area formulas isolates the exceptional image.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace GlobeFlattening

private abbrev globeDomain : Set (ℝ × ℝ) :=
  chartRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)

private abbrev globeBox : Set (ℝ × ℝ) :=
  chartClosedRectangle (-Real.pi) Real.pi (-(Real.pi / 2)) (Real.pi / 2)

private theorem isOpen_globeDomain : IsOpen globeDomain :=
  isOpen_chartRectangle _ _ _ _

/-- On every open rectangle with closure inside the cut-sphere chart,
the exceptional image has positive planar measure. -/
theorem volume_local_exceptional_image_pos {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hbox : chartClosedRectangle a b c d ⊆ globeDomain)
    (hu : ContinuousOn u globeBox)
    (hslope : ∀ p ∈ globeBox, ∀ q ∈ globeBox,
      p.2 = q.2 → p.1 < q.1 → Real.cos p.2 * (q.1 - p.1) < u q - u p)
    (hgood : MeasurableSet good) (hnull : volume (globeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p) :
    0 < volume (flattenCoordinates u '' (chartRectangle a b c d \ good)) := by
  let R := chartRectangle a b c d
  let U := fun y => u (b, y) - u (a, y)
  let L := fun y => (b - a) * Real.cos y
  have hR : IsOpen R := isOpen_chartRectangle _ _ _ _
  have hsub := hbox.trans chartRectangle_subset_closed
  have hRsub := chartRectangle_subset_closed.trans hbox
  have hRectNull : volume (R \ good) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left hRsub) hnull
  have hcos : ∀ y ∈ Ioo c d, 0 < Real.cos y := by
    intro y hy
    have hp : (a, y) ∈ chartClosedRectangle a b c d :=
      ⟨⟨le_rfl, hab.le⟩, Ioo_subset_Icc_self hy⟩
    exact Real.cos_pos_of_mem_Ioo (hbox hp).2
  have hLcon : Continuous L := continuous_const.mul Real.continuous_cos
  have hRow (x : ℝ) (hx : x ∈ Icc a b) : ContinuousOn (fun y => u (x, y)) (Icc c d) :=
    (hu.mono hsub).comp' ((continuous_const.prodMk continuous_id).continuousOn)
      (fun _ hy => ⟨hx, hy⟩)
  have hUcon : ContinuousOn U (Icc c d) := (hRow b ⟨hab.le, le_rfl⟩).sub (hRow a ⟨le_rfl, hab.le⟩)
  have hUInt : IntegrableOn U (Ioo c d) := hUcon.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hLInt : IntegrableOn L (Ioo c d) := hLcon.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hLU : ∀ y ∈ Icc c d, L y < U y := by
    intro y hy
    simpa only [L, U, mul_comm (b - a)] using
      hslope (a, y) (hsub ⟨⟨le_rfl, hab.le⟩, hy⟩) (b, y) (hsub ⟨⟨hab.le, le_rfl⟩, hy⟩) rfl hab
  have hLnn : 0 ≤ᵐ[volume.restrict (Ioo c d)] L :=
    (ae_restrict_mem measurableSet_Ioo).mono (fun y hy => mul_nonneg (sub_nonneg.mpr hab.le) (hcos y hy).le)
  have hUnn : 0 ≤ᵐ[volume.restrict (Ioo c d)] U :=
    (hLnn.and (ae_restrict_mem measurableSet_Ioo)).mono
      (fun y hy => hy.1.trans (hLU y (Ioo_subset_Icc_self hy.2)).le)
  have hreal : (∫ y in Ioo c d, L y) < ∫ y in Ioo c d, U y := by
    simp_rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hcd.le]
    exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hcd
      hLcon.continuousOn hUcon (fun y hy => (hLU y (Ioc_subset_Icc_self hy)).le)
      ⟨c, ⟨le_rfl, hcd.le⟩, hLU c ⟨le_rfl, hcd.le⟩⟩
  have hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b) := by
    intro y hy x₁ hx₁ x₂ hx₂ hx
    have hlo := hslope (x₁, y) (hsub ⟨hx₁, Ioo_subset_Icc_self hy⟩)
      (x₂, y) (hsub ⟨hx₂, Ioo_subset_Icc_self hy⟩) rfl hx
    exact sub_pos.mp ((mul_pos (hcos y hy) (sub_pos.mpr hx)).trans hlo)
  have hinj : InjOn (flattenCoordinates u) R := (triangularChart hab.le (hu.mono hsub) hmono).injOn
  have hAreaLt : volume (flattenCoordinates u '' (R ∩ good)) <
      volume (flattenCoordinates u '' R) := by
    rw [measure_flattened_good_image (hR.measurableSet.inter hgood) inter_subset_left
        (by rwa [sdiff_self_inter]) hinj
        (fun p hp => (hderiv p hp.2).hasFDerivWithinAt) (fun p hp => (hcos p.2 hp.1.2).le),
      lintegral_cos_rectangle hab.le,
      ← ofReal_integral_eq_lintegral_ofReal hLInt hLnn, show R = chartRectangle a b c d from rfl,
      image_flattenCoordinates_chartRectangle hab.le (hu.mono hsub) hmono,
      volume_chartImage_eq_lintegral_width hab.le (hu.mono hsub),
      ← ofReal_integral_eq_lintegral_ofReal hUInt hUnn]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (integral_nonneg_of_ae hLnn)).mpr hreal
  by_contra! hnpos
  have hazero : volume (flattenCoordinates u '' (R \ good)) = 0 := le_antisymm hnpos bot_le
  have hsplit := measure_union_le (μ := volume) (flattenCoordinates u '' (R ∩ good))
    (flattenCoordinates u '' (R \ good))
  rw [← image_union, inter_union_sdiff, hazero, add_zero] at hsplit
  exact hAreaLt.not_ge hsplit

/-- Every nonempty open subset of the planar image meets the exceptional
image in a set of positive area. -/
theorem volume_exceptional_inter_of_open {u : ℝ × ℝ → ℝ} {good W : Set (ℝ × ℝ)}
    (hu : ContinuousOn u globeBox)
    (hslope : ∀ p ∈ globeBox, ∀ q ∈ globeBox,
      p.2 = q.2 → p.1 < q.1 → Real.cos p.2 * (q.1 - p.1) < u q - u p)
    (hgood : MeasurableSet good) (hnull : volume (globeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p)
    (hW : IsOpen W) (hne : W.Nonempty) (hWsub : W ⊆ flattenCoordinates u '' globeDomain) :
    0 < volume (W ∩ flattenCoordinates u '' (globeDomain \ good)) := by
  let V := globeDomain ∩ flattenCoordinates u ⁻¹' W
  have hcont : ContinuousOn (flattenCoordinates u) globeDomain :=
    (hu.mono chartRectangle_subset_closed).prodMk continuous_snd.continuousOn
  have hV : IsOpen V := hcont.isOpen_inter_preimage isOpen_globeDomain hW
  have hVne : V.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    obtain ⟨p, hp, rfl⟩ := hWsub hq
    exact ⟨p, hp, hq⟩
  obtain ⟨p, hp⟩ := hVne
  obtain ⟨a, b, c, d, hp', hsub⟩ := exists_chartClosedRectangle_subset_of_mem_nhds (hV.mem_nhds hp)
  have hbox : chartClosedRectangle a b c d ⊆ globeDomain := hsub.trans inter_subset_left
  refine (volume_local_exceptional_image_pos (hp'.1.1.trans hp'.1.2) (hp'.2.1.trans hp'.2.2)
    hbox hu hslope hgood hnull hderiv).trans_le (measure_mono ?_)
  rintro _ ⟨p, hp, rfl⟩
  have hpV := hsub (chartRectangle_subset_closed hp.1)
  exact ⟨hpV.2, ⟨p, ⟨hpV.1, hp.2⟩, rfl⟩⟩

end GlobeFlattening
