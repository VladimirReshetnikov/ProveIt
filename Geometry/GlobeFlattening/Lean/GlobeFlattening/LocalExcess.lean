import GlobeFlattening.CoordinateArea
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Strict local excess in the flattening chart

A rectangle on which the image area is exactly the cosine-weighted area
would force the scalar function to have the form `x cos y + k y`.
The vertical derivatives at two good points of one row rule this out.
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
  apply ae_neBot.mpr
  intro hzero
  have hmass := Measure.measure_univ_eq_zero.mpr hzero
  rw [Measure.restrict_apply_univ, Real.volume_Ioo] at hmass
  exact (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)) hmass

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

/-- The difference of two longitude values cannot agree with a fixed
nonzero multiple of cosine throughout a rectangle. -/
private theorem not_cosine_row_difference {u : ℝ × ℝ → ℝ} {good : Set (ℝ × ℝ)}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hbox : chartClosedRectangle a b c d ⊆ globeDomain)
    (hgood : MeasurableSet good) (hnull : volume (chartRectangle a b c d \ good) = 0)
    (hderiv : ∀ p ∈ good, HasFDerivAt u
      (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p)
    (hdiff : ∀ y ∈ Ioo c d, ∀ x₁ ∈ Ioo a b, ∀ x₂ ∈ Ioo a b,
      u (x₂, y) - u (x₁, y) = (x₂ - x₁) * Real.cos y) : False := by
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
    have hlow : -Real.pi < y := by linarith [hyLat.1, Real.pi_pos]
    have hhigh : y < Real.pi := by linarith [hyLat.2, Real.pi_pos]
    exact fun hz => hy0 ((Real.sin_eq_zero_iff_of_lt_of_lt hlow hhigh).mp hz)
  have hv₁ := zero_vertical_derivative (hderiv (x₁, y) hp₁)
  have hv₂ := zero_vertical_derivative (hderiv (x₂, y) hp₂)
  have hzero := hv₂.sub hv₁
  have hsub : (fun t => u (x₂, t)) - (fun t => u (x₁, t)) =
      (fun t => u (x₂, t) - u (x₁, t)) := rfl
  rw [hsub, sub_self] at hzero
  have hcos : HasDerivAt (fun t => (x₂ - x₁) * Real.cos t)
      ((x₂ - x₁) * -Real.sin y) y := (Real.hasDerivAt_cos y).const_mul _
  have hnear : ∀ᶠ t in 𝓝 y, t ∈ Ioo c d := isOpen_Ioo.mem_nhds hy
  have heq : (fun t => u (x₂, t) - u (x₁, t)) =ᶠ[𝓝 y]
      (fun t => (x₂ - x₁) * Real.cos t) :=
    hnear.mono (fun t ht => hdiff t ht x₁ hx₁ x₂ hx₂)
  exact (mul_ne_zero (sub_ne_zero.mpr hne) (neg_ne_zero.mpr hsin))
    ((hcos.congr_of_eventuallyEq heq).unique hzero)

private theorem lintegral_cos_rectangle {a b c d : ℝ} (hab : a ≤ b) :
    (∫⁻ p in chartRectangle a b c d, ENNReal.ofReal (Real.cos p.2)) =
      ∫⁻ y in Ioo c d, ENNReal.ofReal ((b - a) * Real.cos y) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.cos p.2)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_cos.measurable.comp measurable_snd)
  rw [chartRectangle, Measure.volume_eq_prod, setLIntegral_prod_symm _ hmeas.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro y _
  change (∫⁻ _ in Ioo a b, ENNReal.ofReal (Real.cos y)) = _
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, mul_comm]
  exact (ENNReal.ofReal_mul (sub_nonneg.mpr hab)).symm

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
  refine not_cosine_row_difference hab hcd hbox hgood hnull hderiv ?_
  intro y hy x₁ hx₁ x₂ hx₂
  have ha : (a, y) ∈ chartClosedRectangle a b c d :=
    ⟨⟨le_rfl, hab.le⟩, Ioo_subset_Icc_self hy⟩
  have hb : (b, y) ∈ chartClosedRectangle a b c d :=
    ⟨⟨hab.le, le_rfl⟩, Ioo_subset_Icc_self hy⟩
  have hlinear (x : ℝ) (hx : x ∈ Ioo a b) :
      u (x, y) - u (a, y) = Real.cos y * (x - a) := by
    have hxy : (x, y) ∈ chartClosedRectangle a b c d :=
      ⟨Ioo_subset_Icc_self hx, Ioo_subset_Icc_self hy⟩
    have hlo := hslope (a, y) ha (x, y) hxy rfl hx.1.le
    have hhi := hslope (x, y) hxy (b, y) hb rfl hx.2.le
    linarith only [hlo, hhi, hbad y hy]
  linarith only [hlinear x₁ hx₁, hlinear x₂ hx₂]

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
  have hLU : ∀ y ∈ Ioo c d, L y ≤ U y := by
    intro y hy
    have ha : (a, y) ∈ chartClosedRectangle a b c d :=
      ⟨⟨le_rfl, hab.le⟩, Ioo_subset_Icc_self hy⟩
    have hb : (b, y) ∈ chartClosedRectangle a b c d :=
      ⟨⟨hab.le, le_rfl⟩, Ioo_subset_Icc_self hy⟩
    simpa only [L, U, mul_comm (b - a)] using hslope (a, y) (hsub ha) (b, y) (hsub hb) rfl hab.le
  have hLnn : 0 ≤ᵐ[volume.restrict (Ioo c d)] L :=
    (ae_restrict_mem measurableSet_Ioo).mono (fun y hy => mul_nonneg (sub_nonneg.mpr hab.le) (hcos y hy).le)
  have hUnn : 0 ≤ᵐ[volume.restrict (Ioo c d)] U :=
    (hLnn.and (ae_restrict_mem measurableSet_Ioo)).mono (fun y hy => hy.1.trans (hLU y hy.2))
  have hreal : (∫ y in Ioo c d, L y) < ∫ y in Ioo c d, U y := by
    by_contra! hle
    have hzero : (∫ y in Ioo c d, U y - L y) = 0 := by
      rw [integral_sub hUInt hLInt]
      linarith only [hle, setIntegral_mono_on hLInt hUInt measurableSet_Ioo hLU]
    have hnneg : 0 ≤ᵐ[volume.restrict (Ioo c d)] (fun y => U y - L y) :=
      (ae_restrict_mem measurableSet_Ioo).mono (fun y hy => sub_nonneg.mpr (hLU y hy))
    have haezero := (integral_eq_zero_iff_of_nonneg_ae hnneg (hUInt.sub hLInt)).mp hzero
    have hEqOn := Measure.eqOn_open_of_ae_eq haezero isOpen_Ioo
      ((hUcon.mono Ioo_subset_Icc_self).sub hLcon.continuousOn) continuousOn_const
    obtain ⟨y, hy, hlt⟩ := exists_strict_width hab hcd hbox
      (fun p hp q hq => hslope p (hsub hp) q (hsub hq)) hgood hRectNull hderiv
    exact (sub_pos.mpr hlt).ne' (hEqOn hy)
  have hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b) := by
    intro y hy x₁ hx₁ x₂ hx₂ hx
    have hlo := hslope (x₁, y) (hsub ⟨hx₁, Ioo_subset_Icc_self hy⟩)
      (x₂, y) (hsub ⟨hx₂, Ioo_subset_Icc_self hy⟩) rfl hx.le
    exact sub_pos.mp ((mul_pos (hcos y hy) (sub_pos.mpr hx)).trans_le hlo)
  have hArea : volume (flattenCoordinates u '' R) = ENNReal.ofReal (∫ y in Ioo c d, U y) := by
    rw [show R = chartRectangle a b c d from rfl,
      image_flattenCoordinates_chartRectangle hab.le (hu.mono hsub) hmono,
      volume_chartImage_eq_lintegral_width hab.le (hu.mono hsub),
      ofReal_integral_eq_lintegral_ofReal hUInt hUnn]
  have hinj : InjOn (flattenCoordinates u) R := by
    apply injOn_flattenCoordinates
    rintro ⟨x₁, y₁⟩ hp ⟨x₂, y₂⟩ hq hlat hx
    change y₁ = y₂ at hlat
    subst y₂
    exact hmono _ hp.2 (Ioo_subset_Icc_self hp.1) (Ioo_subset_Icc_self hq.1) hx
  have hAreaGood : volume (flattenCoordinates u '' (R ∩ good)) =
      ENNReal.ofReal (∫ y in Ioo c d, L y) := by
    rw [measure_flattened_good_image (hR.measurableSet.inter hgood) inter_subset_left
        (by rwa [sdiff_self_inter]) hinj
        (fun p hp => (hderiv p hp.2).hasFDerivWithinAt) (fun p hp => (hcos p.2 hp.1.2).le),
      lintegral_cos_rectangle hab.le,
      ofReal_integral_eq_lintegral_ofReal hLInt hLnn]
  have hAreaLt : volume (flattenCoordinates u '' (R ∩ good)) <
      volume (flattenCoordinates u '' R) := by
    rw [hAreaGood, hArea]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [integral_nonneg_of_ae hLnn])).mpr hreal
  by_contra! hnpos
  have hazero : volume (flattenCoordinates u '' (R \ good)) = 0 := le_antisymm hnpos bot_le
  apply hAreaLt.not_ge
  calc
    _ = volume (flattenCoordinates u '' (R ∩ good) ∪ flattenCoordinates u '' (R \ good)) := by
      rw [← image_union, inter_union_sdiff]
    _ ≤ _ := by simpa only [hazero, add_zero] using
      (measure_union_le (μ := volume) (flattenCoordinates u '' (R ∩ good))
        (flattenCoordinates u '' (R \ good)))

private theorem exists_closed_subrectangle {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ a b c d : ℝ, a < b ∧ c < d ∧ chartClosedRectangle a b c d ⊆ W := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW p hp
  refine ⟨p.1 - r / 2, p.1 + r / 2, p.2 - r / 2, p.2 + r / 2, by linarith, by linarith, ?_⟩
  intro q hq
  have hx : p.1 - r / 2 ≤ q.1 ∧ q.1 ≤ p.1 + r / 2 := hq.1
  have hy : p.2 - r / 2 ≤ q.2 ∧ q.2 ≤ p.2 + r / 2 := hq.2
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  exact ⟨abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩

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
