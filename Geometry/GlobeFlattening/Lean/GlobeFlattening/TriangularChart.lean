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
  have hleftOn : ContinuousOn (fun y => u (a, y)) (Ioo c d) :=
    (continuousOn_latitudeProfile hu ⟨le_rfl, hab⟩).mono Ioo_subset_Icc_self
  have hrightOn : ContinuousOn (fun y => u (b, y)) (Ioo c d) :=
    (continuousOn_latitudeProfile hu ⟨hab, le_rfl⟩).mono Ioo_subset_Icc_self
  have hleft : ContinuousAt (fun q : ℝ × ℝ => u (a, q.2)) p :=
    (hleftOn.continuousAt hlat).comp continuous_snd.continuousAt
  have hright : ContinuousAt (fun q : ℝ × ℝ => u (b, q.2)) p :=
    (hrightOn.continuousAt hlat).comp continuous_snd.continuousAt
  have hy : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.2 ∈ Ioo c d :=
    continuous_snd.continuousAt.tendsto.eventually_mem hlat
  filter_upwards [hy, hleft.eventually_lt continuous_fst.continuousAt hp.2.1,
    continuous_fst.continuousAt.eventually_lt hright hp.2.2] with q hq hlow hhigh
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

private theorem mem_chartRectangle_of_mem_chartImage {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    {p : ℝ × ℝ} (hp : p ∈ chartClosedRectangle a b c d)
    (hq : flattenCoordinates u p ∈ chartImage u a b c d) :
    p ∈ chartRectangle a b c d := by
  rcases p with ⟨x, y⟩
  have hxc : x ∈ Icc a b := hp.1
  obtain ⟨hy, hleft, hright⟩ :
      y ∈ Ioo c d ∧ u (a, y) < u (x, y) ∧ u (x, y) < u (b, y) := hq
  have hxa : a < x := hxc.1.lt_of_ne fun h => hleft.ne (by rw [h])
  have hxb : x < b := hxc.2.lt_of_ne fun h => hright.ne (by rw [h])
  exact ⟨⟨hxa, hxb⟩, hy⟩

/-- The scalar flattening is a homeomorphism from the open rectangle to the
open region between its endpoint profiles. For inverse continuity, use the
closed images of compact subsets of the closed rectangle. A point in that
rectangle which maps into the target already belongs to the open rectangle. -/
noncomputable def triangularChart {u : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (chartClosedRectangle a b c d))
    (hmono : ∀ y ∈ Ioo c d, StrictMonoOn (fun x => u (x, y)) (Icc a b)) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := by
  let s := chartRectangle a b c d
  let t := chartImage u a b c d
  have hG : ContinuousOn (flattenCoordinates u) (chartClosedRectangle a b c d) :=
    hu.prodMk continuous_snd.continuousOn
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
  have hclosed : IsClosedMap e.toEquiv := by
    intro V hV
    obtain ⟨C, hC, hCV⟩ := isClosed_induced_iff.mp hV
    have hCompact : IsCompact (chartClosedRectangle a b c d ∩ C) :=
      (isCompact_chartClosedRectangle a b c d).inter_right hC
    refine isClosed_induced_iff.mpr ⟨flattenCoordinates u '' (chartClosedRectangle a b c d ∩ C),
      (hCompact.image_of_continuousOn (hG.mono inter_subset_left)).isClosed, ?_⟩
    ext q
    constructor
    · rintro ⟨p, hp, hpq⟩
      have hpo := mem_chartRectangle_of_mem_chartImage hp.1 (by rw [hpq]; exact q.2)
      let p' : s := ⟨p, hpo⟩
      exact ⟨p', hCV ▸ hp.2, Subtype.ext hpq⟩
    · rintro ⟨p, hp, rfl⟩
      have hpC : p ∈ Subtype.val ⁻¹' C := hCV.symm ▸ hp
      exact ⟨p.1, ⟨chartRectangle_subset_closed p.2, hpC⟩, rfl⟩
  have hcont : Continuous e.toEquiv :=
    (hG.mono chartRectangle_subset_closed).restrict.subtype_mk _
  let H := e.toEquiv.toHomeomorphOfContinuousClosed hcont hclosed
  exact
    { toPartialEquiv := e
      open_source := isOpen_chartRectangle a b c d
      open_target := isOpen_chartImage hab hu
      continuousOn_toFun := hG.mono chartRectangle_subset_closed
      continuousOn_invFun := continuousOn_iff_continuous_restrict.mpr
        (continuous_subtype_val.comp H.symm.continuous) }

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
