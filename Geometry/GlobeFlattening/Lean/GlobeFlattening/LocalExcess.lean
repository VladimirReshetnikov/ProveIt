import GlobeFlattening.CoordinateArea
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Strict local excess in the flattening chart

Equality in the width bound throughout a rectangle would force the
scalar function to have the form `x cos y + v(y)` for a function `v`
of latitude. The vertical derivatives at two good points of one row
rule this out.
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

private theorem ae_restrict_Ioo_neBot {a b : ℝ} (hab : a < b) :
    (ae (volume.restrict (Ioo a b))).NeBot := by
  rw [ae_neBot, ne_eq, Measure.restrict_eq_zero, Real.volume_Ioo]
  exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)

private theorem ae_good_rows {good : Set (ℝ × ℝ)} {a b c d : ℝ}
    (hgood : MeasurableSet good) (hnull : volume (chartRectangle a b c d \ good) = 0) :
    ∀ᵐ y ∂volume.restrict (Ioo c d), ∀ᵐ x ∂volume.restrict (Ioo a b), (x, y) ∈ good := by
  have hae : ∀ᵐ p ∂volume.restrict (chartRectangle a b c d), p ∈ good := by
    apply (ae_restrict_iff' (isOpen_chartRectangle _ _ _ _).measurableSet).2
    rw [ae_iff]
    simpa only [Classical.not_imp, ← Set.mem_sdiff, setOf_mem_eq] using hnull
  rw [chartRectangle, Measure.volume_eq_prod, ← Measure.prod_restrict] at hae
  exact (Measure.ae_ae_comm (p := fun x y => (x, y) ∈ good) hgood).mp
    (Measure.ae_ae_of_ae_prod hae)

private theorem zero_vertical_derivative {u : ℝ × ℝ → ℝ} {x y : ℝ}
    (h : HasFDerivAt u (Real.cos y • ContinuousLinearMap.fst ℝ ℝ ℝ) (x, y)) :
    HasDerivAt (fun t => u (x, t)) 0 y := by
  have hv : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  simpa [Function.comp_def] using h.comp_hasDerivAt y hv

/-- Equality of the width bound on each row would force the difference
of two longitude values to be a nonzero multiple of cosine. -/
private theorem exists_strict_width {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hbox : chartClosedRectangle a b c d ⊆ globeDomain)
    (hslope : ∀ p ∈ chartClosedRectangle a b c d, ∀ q ∈ chartClosedRectangle a b c d,
      p.2 = q.2 → p.1 ≤ q.1 → Real.cos p.2 * (q.1 - p.1) ≤ u q - u p)
    (hgood : MeasurableSet good) (hnull : volume (chartRectangle a b c d \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p) :
    ∃ y ∈ Ioo c d, (b - a) * Real.cos y < u (b, y) - u (a, y) := by
  by_contra! hbad
  letI := ae_restrict_Ioo_neBot hcd
  have hyGood : ∀ᵐ y ∂volume.restrict (Ioo c d),
      y ∈ Ioo c d ∧ y ≠ 0 ∧ ∀ᵐ x ∂volume.restrict (Ioo a b), (x, y) ∈ good := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, (volume.restrict (Ioo c d)).ae_ne 0,
      ae_good_rows hgood hnull] with y hy hne hg
    exact ⟨hy, hne, hg⟩
  obtain ⟨y, hy, hy0, hyGood⟩ := hyGood.exists
  letI := ae_restrict_Ioo_neBot hab
  have hxGood : ∀ᵐ x ∂volume.restrict (Ioo a b), x ∈ Ioo a b ∧ (x, y) ∈ good :=
    (ae_restrict_mem measurableSet_Ioo).and hyGood
  obtain ⟨x₁, hx₁, hp₁⟩ := hxGood.exists
  obtain ⟨x₂, ⟨hx₂, hp₂⟩, hne⟩ := (hxGood.and ((volume.restrict (Ioo a b)).ae_ne x₁)).exists
  have hxy : (x₁, y) ∈ chartClosedRectangle a b c d :=
    ⟨Ioo_subset_Icc_self hx₁, Ioo_subset_Icc_self hy⟩
  have hyLat : y ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := (hbox hxy).2
  have hsin : Real.sin y ≠ 0 := by
    rw [Ne, Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hyLat.1, Real.pi_pos])
      (by linarith [hyLat.2, Real.pi_pos])]
    exact hy0
  have hzero : HasDerivAt (fun t => u (x₂, t) - u (x₁, t)) 0 y := by
    change HasDerivAt ((fun t => u (x₂, t)) - fun t => u (x₁, t)) 0 y
    simpa only [sub_self] using
      (zero_vertical_derivative (hderiv (x₂, y) hp₂)).sub
        (zero_vertical_derivative (hderiv (x₁, y) hp₁))
  have hcos : HasDerivAt (fun t => (x₂ - x₁) * Real.cos t)
      ((x₂ - x₁) * -Real.sin y) y := (Real.hasDerivAt_cos y).const_mul _
  have heq : (fun t => u (x₂, t) - u (x₁, t)) =ᶠ[𝓝 y]
      (fun t => (x₂ - x₁) * Real.cos t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    have ha : (a, t) ∈ chartClosedRectangle a b c d := ⟨⟨le_rfl, hab.le⟩, Ioo_subset_Icc_self ht⟩
    have hb : (b, t) ∈ chartClosedRectangle a b c d := ⟨⟨hab.le, le_rfl⟩, Ioo_subset_Icc_self ht⟩
    have hlinear {x : ℝ} (hx : x ∈ Ioo a b) : u (x, t) - u (a, t) = Real.cos t * (x - a) := by
      have hp : (x, t) ∈ chartClosedRectangle a b c d :=
        ⟨Ioo_subset_Icc_self hx, Ioo_subset_Icc_self ht⟩
      linarith only [hslope (a, t) ha (x, t) hp rfl hx.1.le,
        hslope (x, t) hp (b, t) hb rfl hx.2.le, hbad t ht]
    linarith only [hlinear hx₁, hlinear hx₂]
  exact (mul_ne_zero (sub_ne_zero.mpr hne) (neg_ne_zero.mpr hsin))
    ((hcos.congr_of_eventuallyEq heq).unique hzero)

/-- On every open rectangle with closure inside the cut-sphere chart,
the exceptional image has positive planar measure. -/
theorem volume_local_exceptional_image_pos {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hbox : chartClosedRectangle a b c d ⊆ globeDomain)
    (hu : ContinuousOn u globeBox)
    (hslope : ∀ p ∈ globeBox, ∀ q ∈ globeBox,
      p.2 = q.2 → p.1 ≤ q.1 → Real.cos p.2 * (q.1 - p.1) ≤ u q - u p)
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
  have hLU : ∀ y ∈ Icc c d, L y ≤ U y := by
    intro y hy
    simpa only [L, U, mul_comm (b - a)] using
      hslope (a, y) (hsub ⟨⟨le_rfl, hab.le⟩, hy⟩) (b, y) (hsub ⟨⟨hab.le, le_rfl⟩, hy⟩) rfl hab.le
  have hLnn : 0 ≤ᵐ[volume.restrict (Ioo c d)] L :=
    (ae_restrict_mem measurableSet_Ioo).mono (fun y hy => mul_nonneg (sub_nonneg.mpr hab.le) (hcos y hy).le)
  have hUnn : 0 ≤ᵐ[volume.restrict (Ioo c d)] U :=
    (hLnn.and (ae_restrict_mem measurableSet_Ioo)).mono
      (fun y hy => hy.1.trans (hLU y (Ioo_subset_Icc_self hy.2)))
  have hreal : (∫ y in Ioo c d, L y) < ∫ y in Ioo c d, U y := by
    simp_rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hcd.le]
    obtain ⟨y, hy, hlt⟩ := exists_strict_width hab hcd hbox
      (fun p hp q hq => hslope p (hsub hp) q (hsub hq)) hgood hRectNull hderiv
    exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hcd
      hLcon.continuousOn hUcon (fun y hy => hLU y (Ioc_subset_Icc_self hy)) ⟨y, Ioo_subset_Icc_self hy, hlt⟩
  have hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b) := by
    intro y hy x₁ hx₁ x₂ hx₂ hx
    have hlo := hslope (x₁, y) (hsub ⟨hx₁, Ioo_subset_Icc_self hy⟩)
      (x₂, y) (hsub ⟨hx₂, Ioo_subset_Icc_self hy⟩) rfl hx.le
    exact sub_pos.mp ((mul_pos (hcos y hy) (sub_pos.mpr hx)).trans_le hlo)
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

private theorem exists_closed_subrectangle {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ a b c d : ℝ, a < b ∧ c < d ∧ chartClosedRectangle a b c d ⊆ W := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨a, b, c, d, hp', hbox⟩ :=
    exists_chartClosedRectangle_subset_of_mem_nhds (hW.mem_nhds hp)
  exact ⟨a, b, c, d, hp'.1.1.trans hp'.1.2, hp'.2.1.trans hp'.2.2, hbox⟩

/-- Every nonempty open subset of the planar image meets the exceptional
image in a set of positive area. -/
theorem volume_exceptional_inter_of_open {u : ℝ × ℝ → ℝ} {good W : Set (ℝ × ℝ)}
    (hu : ContinuousOn u globeBox)
    (hslope : ∀ p ∈ globeBox, ∀ q ∈ globeBox,
      p.2 = q.2 → p.1 ≤ q.1 → Real.cos p.2 * (q.1 - p.1) ≤ u q - u p)
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
  obtain ⟨a, b, c, d, hab, hcd, hsub⟩ := exists_closed_subrectangle hV hVne
  have hbox : chartClosedRectangle a b c d ⊆ globeDomain := hsub.trans inter_subset_left
  refine (volume_local_exceptional_image_pos hab hcd hbox hu hslope hgood hnull hderiv).trans_le
    (measure_mono ?_)
  rintro _ ⟨p, hp, rfl⟩
  have hpV := hsub (chartRectangle_subset_closed hp.1)
  exact ⟨hpV.2, ⟨p, ⟨hpV.1, hp.2⟩, rfl⟩⟩

/-- Lipschitz maps in the plane take null sets to null sets. The exceptional
image therefore prevents a Lipschitz bound on any open source patch. -/
theorem not_lipschitzOn_flattenCoordinates_of_open {u : ℝ × ℝ → ℝ} {good W : Set (ℝ × ℝ)}
    (hu : ContinuousOn u globeBox)
    (hslope : ∀ p ∈ globeBox, ∀ q ∈ globeBox,
      p.2 = q.2 → p.1 ≤ q.1 → Real.cos p.2 * (q.1 - p.1) ≤ u q - u p)
    (hgood : MeasurableSet good) (hnull : volume (globeDomain \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p)
    (hW : IsOpen W) (hne : W.Nonempty) (hWsub : W ⊆ globeDomain) (K : ℝ≥0) :
    ¬ LipschitzOnWith K (flattenCoordinates u) W := by
  intro hlip
  obtain ⟨a, b, c, d, hab, hcd, hsub⟩ := exists_closed_subrectangle hW hne
  have hbox : chartClosedRectangle a b c d ⊆ globeDomain := hsub.trans hWsub
  have hpos := volume_local_exceptional_image_pos hab hcd hbox hu hslope hgood hnull hderiv
  let S := chartRectangle a b c d \ good
  have hS : S ⊆ W := sdiff_subset.trans (chartRectangle_subset_closed.trans hsub)
  have hSnull : volume S = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left (chartRectangle_subset_closed.trans hbox)) hnull
  have hImage := (hlip.mono hS).hausdorffMeasure_image_le (d := 2) (by norm_num)
  rw [hausdorffMeasure_prod_real, hSnull, mul_zero] at hImage
  exact hpos.not_ge hImage

end GlobeFlattening
