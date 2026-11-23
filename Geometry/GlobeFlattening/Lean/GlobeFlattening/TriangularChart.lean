import GlobeFlattening.RestrictedArea
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# The triangular flattening chart

The scalar construction becomes a homeomorphism once it is continuous on
the closed rectangle and strictly increasing on each interior latitude row.
-/

open Filter Set Topology
open scoped Topology

namespace GlobeFlattening

/-- The closed coordinate rectangle, on which the scalar function is continuous. -/
def chartClosedRectangle (a b c d : ℝ) : Set (ℝ × ℝ) :=
  Icc a b ×ˢ Icc c d

/-- The open longitude and latitude rectangle. -/
def chartRectangle (a b c d : ℝ) : Set (ℝ × ℝ) :=
  Ioo a b ×ˢ Ioo c d

/-- The region between the left and right endpoint profiles. -/
def chartImage (u : ℝ × ℝ → ℝ) (a b c d : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Ioo c d ∧ u (a, p.2) < p.1 ∧ p.1 < u (b, p.2)}

theorem chartRectangle_subset_closed {a b c d : ℝ} :
    chartRectangle a b c d ⊆ chartClosedRectangle a b c d :=
  prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

theorem isOpen_chartRectangle (a b c d : ℝ) : IsOpen (chartRectangle a b c d) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem isCompact_chartClosedRectangle (a b c d : ℝ) :
    IsCompact (chartClosedRectangle a b c d) :=
  isCompact_Icc.prod isCompact_Icc

/-- Every neighborhood contains a closed rectangle with the point in its interior. -/
theorem exists_chartClosedRectangle_subset_of_mem_nhds {p : ℝ × ℝ} {W : Set (ℝ × ℝ)}
    (hW : W ∈ 𝓝 p) :
    ∃ a b c d : ℝ, p ∈ chartRectangle a b c d ∧ chartClosedRectangle a b c d ⊆ W := by
  obtain ⟨U, hU, V, hV, hsub⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨a, b, _, hab, hUa⟩ := exists_Icc_mem_subset_of_mem_nhds hU
  obtain ⟨c, d, _, hcd, hVc⟩ := exists_Icc_mem_subset_of_mem_nhds hV
  exact ⟨a, b, c, d, ⟨Icc_mem_nhds_iff.mp hab, Icc_mem_nhds_iff.mp hcd⟩,
    (prod_mono hUa hVc).trans hsub⟩

private theorem continuousOn_longitudeRow {u : ℝ × ℝ → ℝ} {a b c d y : ℝ}
    (hu : ContinuousOn u (chartClosedRectangle a b c d)) (hy : y ∈ Icc c d) :
    ContinuousOn (fun x => u (x, y)) (Icc a b) :=
  hu.comp' ((continuous_id.prodMk continuous_const).continuousOn)
    (fun _ hx => ⟨hx, hy⟩)

private theorem continuousOn_latitudeProfile {u : ℝ × ℝ → ℝ} {a b c d x : ℝ}
    (hu : ContinuousOn u (chartClosedRectangle a b c d)) (hx : x ∈ Icc a b) :
    ContinuousOn (fun y => u (x, y)) (Icc c d) :=
  hu.comp' ((continuous_const.prodMk continuous_id).continuousOn)
    (fun _ hy => ⟨hx, hy⟩)

theorem isOpen_chartImage {u : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (chartClosedRectangle a b c d)) :
    IsOpen (chartImage u a b c d) := by
  refine isOpen_iff_mem_nhds.2 (fun p hp => ?_)
  have hlat : Ioo c d ∈ 𝓝 p.2 := isOpen_Ioo.mem_nhds hp.1
  have hprofile (x : ℝ) (hx : x ∈ Icc a b) :
      ContinuousAt (fun q : ℝ × ℝ => u (x, q.2)) p :=
    (((continuousOn_latitudeProfile hu hx).mono Ioo_subset_Icc_self).continuousAt hlat).comp
      continuous_snd.continuousAt
  have hy : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.2 ∈ Ioo c d :=
    continuous_snd.continuousAt.tendsto.eventually_mem hlat
  filter_upwards [hy, (hprofile a ⟨le_rfl, hab⟩).eventually_lt continuous_fst.continuousAt hp.2.1,
    continuous_fst.continuousAt.eventually_lt (hprofile b ⟨hab, le_rfl⟩) hp.2.2] with q hq hlow hhigh
  exact ⟨hq, hlow, hhigh⟩

theorem image_flattenCoordinates_chartRectangle {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b)) :
    flattenCoordinates u '' chartRectangle a b c d = chartImage u a b c d := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpx : p.1 ∈ Ioo a b := hp.1
    have hpy : p.2 ∈ Ioo c d := hp.2
    exact ⟨hpy, hmono _ hpy ⟨le_rfl, hab⟩ (Ioo_subset_Icc_self hpx) hpx.1,
      hmono _ hpy (Ioo_subset_Icc_self hpx) ⟨hab, le_rfl⟩ hpx.2⟩
  · intro hq
    have hlat : q.2 ∈ Ioo c d := hq.1
    have hrow := continuousOn_longitudeRow hu (Ioo_subset_Icc_self hlat)
    obtain ⟨x, hx, hux⟩ := intermediate_value_Ioo hab hrow
      (show q.1 ∈ Ioo (u (a, q.2)) (u (b, q.2)) from hq.2)
    exact ⟨(x, q.2), ⟨hx, hlat⟩, Prod.ext hux rfl⟩

theorem isBounded_chartImage {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b)) :
    Bornology.IsBounded (chartImage u a b c d) := by
  rw [← image_flattenCoordinates_chartRectangle hab hu hmono]
  exact (((isCompact_chartClosedRectangle a b c d).image_of_continuousOn
    (hu.prodMk continuous_snd.continuousOn)).isBounded).subset
      (image_mono chartRectangle_subset_closed)

private theorem isOpen_image_flattenCoordinates {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b))
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hsub : W ⊆ chartRectangle a b c d) :
    IsOpen (flattenCoordinates u '' W) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨a', b', c', d', hp', hbox⟩ :=
    exists_chartClosedRectangle_subset_of_mem_nhds (hW.mem_nhds hp)
  have hrect := hbox.trans hsub
  have hab' : a' ≤ b' := (hp'.1.1.trans hp'.1.2).le
  have hmono' : ∀ y ∈ Ioo c' d', StrictMonoOn (fun x => u (x, y)) (Icc a' b') := by
    intro y hy x hx z hz hxz
    have hx' : (x, y) ∈ chartRectangle a b c d := hrect ⟨hx, Ioo_subset_Icc_self hy⟩
    have hz' : (z, y) ∈ chartRectangle a b c d := hrect ⟨hz, Ioo_subset_Icc_self hy⟩
    exact hmono y hx'.2 (Ioo_subset_Icc_self hx'.1) (Ioo_subset_Icc_self hz'.1) hxz
  have hopen : IsOpen (flattenCoordinates u '' chartRectangle a' b' c' d') := by
    have hu' := hu.mono (hrect.trans chartRectangle_subset_closed)
    rw [image_flattenCoordinates_chartRectangle hab' hu' hmono']
    exact isOpen_chartImage hab' hu'
  exact mem_of_superset (hopen.mem_nhds (mem_image_of_mem _ hp'))
    (image_mono (chartRectangle_subset_closed.trans hbox))

/-- The scalar flattening is a homeomorphism from the open rectangle to the
open region between its endpoint profiles. It is open because each point
of an open patch lies inside a smaller rectangle whose image is open. -/
noncomputable def triangularChart {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b)) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := by
  let s := chartRectangle a b c d
  let t := chartImage u a b c d
  have hcont : ContinuousOn (flattenCoordinates u) s :=
    (hu.mono chartRectangle_subset_closed).prodMk continuous_snd.continuousOn
  have hinj : InjOn (flattenCoordinates u) s := by
    apply injOn_flattenCoordinates
    intro p hp q hq hlat hlt
    rcases p with ⟨x, y⟩
    rcases q with ⟨x', y'⟩
    change y = y' at hlat
    subst y'
    exact hmono y hp.2 (Ioo_subset_Icc_self hp.1) (Ioo_subset_Icc_self hq.1) hlt
  have hbij : BijOn (flattenCoordinates u) s t := by
    change BijOn (flattenCoordinates u) (chartRectangle a b c d) (chartImage u a b c d)
    rw [← image_flattenCoordinates_chartRectangle hab hu hmono]
    exact hinj.bijOn_image
  let e := hbij.toPartialEquiv (flattenCoordinates u) s t
  have hs : IsOpen s := isOpen_chartRectangle a b c d
  refine OpenPartialHomeomorph.ofContinuousOpenRestrict e hcont ?_ hs
  change IsOpenMap (fun p : s => flattenCoordinates u p)
  intro V hV
  have hsub : Subtype.val '' V ⊆ s := by rintro _ ⟨q, _, rfl⟩; exact q.2
  simpa only [image_image] using
    isOpen_image_flattenCoordinates hu hmono (hs.isOpenMap_subtype_val V hV) hsub

@[simp] theorem triangularChart_source {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b)) :
    (triangularChart hab hu hmono).source = chartRectangle a b c d := rfl

@[simp] theorem triangularChart_target {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b)) :
    (triangularChart hab hu hmono).target = chartImage u a b c d := rfl

@[simp] theorem triangularChart_apply {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b))
    (p : ℝ × ℝ) : triangularChart hab hu hmono p = flattenCoordinates u p := rfl

end GlobeFlattening
