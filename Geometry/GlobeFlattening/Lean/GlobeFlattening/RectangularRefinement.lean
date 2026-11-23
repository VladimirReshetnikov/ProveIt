import GlobeFlattening.RectangularMesh
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# One rectangular refinement

The slope chosen in a row is the target slope at its midpoint plus one mesh
width. The Lipschitz bound on the target makes this a majorant across the
whole row and adjacent layers. This gives the same slack estimates as the
row maximum used in the report.
-/

open Set

namespace GlobeFlattening.RectangularMesh

noncomputable section

variable (g : RectangularMesh)

def rowSlope (target : ℝ → ℝ) (j : ℕ) : ℝ := target (g.midlatitude j) + g.width

def rowRefinement (old : ℝ × ℝ → ℝ) (target : ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  stripProfile g.left g.width (g.width - g.margin) (g.rowSlope target j) g.columns
    (fun x => old (x, g.midlatitude j))

def refineStage (old : ℝ × ℝ → ℝ) (target : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  latitudeProfile g.layerStart (2 * g.margin) g.transitions (g.rowRefinement old target)

/-- A lower bound on every secant slope of a horizontal row of the rectangle. -/
def HasLowerSlope (u : ℝ × ℝ → ℝ) (target : ℝ → ℝ) : Prop :=
  ∀ y ∈ Icc g.bottom (g.latitude (g.transitions + 1)),
    ∀ x₁ ∈ Icc g.left (g.longitude g.columns),
    ∀ x₂ ∈ Icc g.left (g.longitude g.columns), x₁ ≤ x₂ →
      target y * (x₂ - x₁) ≤ u (x₂, y) - u (x₁, y)

theorem hasLowerSlope_iff_same_latitude {u : ℝ × ℝ → ℝ} {target : ℝ → ℝ} :
    g.HasLowerSlope u target ↔
      ∀ p ∈ g.rectangle, ∀ q ∈ g.rectangle, p.2 = q.2 → p.1 ≤ q.1 →
        target p.2 * (q.1 - p.1) ≤ u q - u p := by
  constructor
  · intro h p hp q hq hlat hlong
    obtain ⟨x, y⟩ := p
    obtain ⟨x', y'⟩ := q
    change y = y' at hlat
    subst y'
    exact h y hp.2 x hp.1 x' hq.1 hlong
  · intro h y hy x hx x' hx' hlong
    exact h (x, y) ⟨hx, hy⟩ (x', y) ⟨hx', hy⟩ rfl hlong

theorem continuous_refineStage (old : ℝ × ℝ → ℝ) (target : ℝ → ℝ) :
    Continuous (g.refineStage old target) :=
  continuous_latitudeProfile _ _ _ fun _ => continuous_stripProfile _ _ _ _ _ _

theorem rowSlope_bounds {target : ℝ → ℝ}
    (hlip : ∀ y z : ℝ, |target y - target z| ≤ |y - z|)
    {y : ℝ} {j : ℕ} (hclose : |y - g.midlatitude j| ≤ g.width) :
    target y ≤ g.rowSlope target j ∧ g.rowSlope target j ≤ target y + 2 * g.width := by
  have h := abs_le.mp ((hlip y (g.midlatitude j)).trans hclose)
  unfold rowSlope
  constructor <;> linarith

private theorem cell_rise {old : ℝ × ℝ → ℝ} {target previous : ℝ → ℝ}
    (hold : g.HasLowerSlope old previous)
    (hgap : ∀ y, target y + g.width ≤ previous y)
    {j : ℕ} (hj : j ≤ g.transitions) (i : ℕ) (hi : i < g.columns) :
    g.rowSlope target j * g.width ≤
      old (g.longitude (i + 1), g.midlatitude j) - old (g.longitude i, g.midlatitude j) := by
  have hstep : g.longitude (i + 1) - g.longitude i = g.width := by
    rw [g.longitude_succ, add_sub_cancel_left]
  have hh := hold _ (g.midlatitude_mem hj) _ (g.longitude_mem hi.le)
    _ (g.longitude_mem (Nat.succ_le_of_lt hi)) (g.longitude_mono (Nat.le_succ i))
  rw [hstep] at hh
  exact (mul_le_mul_of_nonneg_right (hgap _) g.width_pos.le).trans hh

theorem refineStage_lowerSlope {old : ℝ × ℝ → ℝ} {target previous : ℝ → ℝ}
    (hold : g.HasLowerSlope old previous)
    (hgap : ∀ y, target y + g.width ≤ previous y)
    (hlip : ∀ y z : ℝ, |target y - target z| ≤ |y - z|) :
    g.HasLowerSlope (g.refineStage old target) target := by
  intro y hy x₁ hx₁ x₂ hx₂ hx
  obtain ⟨i, j, t, hi, hj, ht₀, ht₁, hclosei, hclosej, hblend⟩ :=
    g.exists_latitude_blend (g.rowRefinement old target) hy
  have hrow (l : ℕ) (hl : l ≤ g.transitions) (hclose : |y - g.midlatitude l| ≤ g.width) :
      target y * (x₂ - x₁) ≤ g.rowRefinement old target l x₂ -
        g.rowRefinement old target l x₁ :=
    (mul_le_mul_of_nonneg_right (g.rowSlope_bounds hlip hclose).1 (sub_nonneg.mpr hx)).trans
      (stripProfile_lower_slope (sub_lt_self _ g.margin_pos) (g.cell_rise hold hgap hl) hx)
  change target y * (x₂ - x₁) ≤
    latitudeProfile g.layerStart (2 * g.margin) g.transitions
      (g.rowRefinement old target) (x₂, y) -
    latitudeProfile g.layerStart (2 * g.margin) g.transitions
      (g.rowRefinement old target) (x₁, y)
  rw [hblend x₂, hblend x₁]
  exact latitude_blend_lower_slope ht₀ ht₁ (hrow i hi hclosei) (hrow j hj hclosej)

/-- The good tiles use the long first segment of each row profile. Here
`leftHeight` is the original height at the frozen left endpoint. -/
theorem refineStage_on_core {old : ℝ × ℝ → ℝ} {target : ℝ → ℝ} {i j : ℕ}
    (hi : i < g.columns) (hj : j ≤ g.transitions) {x y : ℝ}
    (hx₁ : g.longitude i ≤ x) (hx₂ : x ≤ g.longitude i + (g.width - g.margin))
    (hy₁ : g.latitude j + g.margin ≤ y) (hy₂ : y ≤ g.latitude (j + 1) - g.margin) :
    g.refineStage old target (x, y) = old (g.longitude i, g.midlatitude j) +
      g.rowSlope target j * (x - g.longitude i) := by
  have hlast : x ≤ g.longitude (i + 1) := by
    rw [g.longitude_succ]
    linarith [g.margin_pos]
  unfold refineStage
  rw [g.interpolate_at_core _ hj hy₁ hy₂]
  unfold rowRefinement
  rw [stripProfile_eq_cellProfile (sub_nonneg.mpr g.margin_lt_width.le)
    (sub_lt_self _ g.margin_pos) hi hx₁ hlast, cellProfile_of_le_cut]
  · rfl
  · change x - g.longitude i ≤ g.width - g.margin
    linarith

/-- Each sample in the active cell and frozen row is within one mesh width
of the point being refined, in the product metric. -/
private theorem rowSample {i j : ℕ} {p : ℝ × ℝ} {x : ℝ}
    (hi : i < g.columns) (hj : j ≤ g.transitions)
    (hp : p.1 ∈ Icc (g.longitude i) (g.longitude (i + 1)))
    (hx : x ∈ Icc (g.longitude i) (g.longitude (i + 1)))
    (hclose : |p.2 - g.midlatitude j| ≤ g.width) :
    (x, g.midlatitude j) ∈ g.rectangle ∧ dist (x, g.midlatitude j) p ≤ g.width := by
  refine ⟨⟨⟨(g.longitude_mem hi.le).1.trans hx.1,
      hx.2.trans (g.longitude_mono (Nat.succ_le_of_lt hi))⟩, g.midlatitude_mem hj⟩, ?_⟩
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
  have ⟨hp₁, hp₂⟩ := hp
  have ⟨hx₁, hx₂⟩ := hx
  exact ⟨abs_le.mpr ⟨by linarith [g.longitude_succ i], by linarith [g.longitude_succ i]⟩,
    (abs_sub_comm _ _).trans_le hclose⟩

/-- An error bound on both nearby row profiles passes through interpolation. -/
private theorem refineStage_error_of_cell_rows {old : ℝ × ℝ → ℝ} {target : ℝ → ℝ}
    {p : ℝ × ℝ} (hp : p ∈ g.rectangle) {bound : ℝ}
    (hrow : ∀ i < g.columns, p.1 ∈ Icc (g.longitude i) (g.longitude (i + 1)) →
      ∀ j ≤ g.transitions, |p.2 - g.midlatitude j| ≤ g.width →
        |g.rowRefinement old target j p.1 - old p| ≤ bound) :
    |g.refineStage old target p - old p| ≤ bound := by
  obtain ⟨i, hi, hcell⟩ := exists_mesh_cell (width := g.width) g.columns_pos hp.1.1 hp.1.2
  obtain ⟨j, k, t, hj, hk, ht₀, ht₁, hclosej, hclosek, hblend⟩ :=
    g.exists_latitude_blend (g.rowRefinement old target) hp.2
  unfold refineStage
  rw [← Prod.eta p, hblend p.1, Prod.eta]
  exact latitude_blend_error ht₀ ht₁ (hrow i hi hcell j hj hclosej) (hrow i hi hcell k hk hclosek)

/-- The uniform change is controlled by the old oscillation over one mesh
width. Both endpoint samples lie within this distance of the given point. -/
theorem refineStage_uniform_error {old : ℝ × ℝ → ℝ} {target previous : ℝ → ℝ} {osc : ℝ}
    (hold : g.HasLowerSlope old previous)
    (hgap : ∀ y, target y + g.width ≤ previous y)
    (hnonneg : ∀ y ∈ Icc g.bottom (g.latitude (g.transitions + 1)), 0 ≤ target y)
    (hosc : ∀ p ∈ g.rectangle, ∀ q ∈ g.rectangle, dist p q ≤ g.width → |old p - old q| ≤ osc)
    {p : ℝ × ℝ} (hp : p ∈ g.rectangle) :
    |g.refineStage old target p - old p| ≤ osc := by
  apply g.refineStage_error_of_cell_rows hp
  intro i hi hcell j hj hclose
  have hmono := g.longitude_mono (Nat.le_succ i)
  obtain ⟨hleft, hdleft⟩ := g.rowSample hi hj hcell ⟨le_rfl, hmono⟩ hclose
  obtain ⟨hright, hdright⟩ := g.rowSample hi hj hcell ⟨hmono, le_rfl⟩ hclose
  have hlo := (abs_le.mp (hosc _ hleft p hp hdleft)).1
  have hhi := (abs_le.mp (hosc _ hright p hp hdright)).2
  have hb : g.rowRefinement old target j p.1 ∈
      Icc (old (g.longitude i, g.midlatitude j)) (old (g.longitude (i + 1), g.midlatitude j)) :=
    stripProfile_cell_bounds (old := fun x => old (x, g.midlatitude j))
    (sub_nonneg.mpr g.margin_lt_width.le) (sub_lt_self _ g.margin_pos)
    (add_nonneg (hnonneg _ (g.midlatitude_mem hj)) g.width_pos.le)
    (g.cell_rise hold hgap hj) hi hcell.1 hcell.2
  obtain ⟨hb₁, hb₂⟩ := hb
  exact abs_le.mpr ⟨by linarith [hb₁], by linarith [hb₂]⟩

/-- Inside an old affine tile, only the change in slope contributes to the
new error. It is enough that the affine and slope conditions hold one mesh
width around the evaluation point in the product metric. -/
theorem refineStage_local_error {old : ℝ × ℝ → ℝ} {target previous : ℝ → ℝ}
    {intercept a accuracy gap : ℝ} {p : ℝ × ℝ} (hp : p ∈ g.rectangle)
    (hgap : ∀ y, target y + g.width ≤ previous y)
    (hgap_upper : ∀ y, previous y ≤ target y + gap)
    (haffine : ∀ q ∈ g.rectangle, dist q p ≤ g.width →
      old q = intercept + a * q.1)
    (haccuracy : ∀ q ∈ g.rectangle, dist q p ≤ g.width →
      previous q.2 ≤ a ∧ a ≤ previous q.2 + accuracy) :
    |g.refineStage old target p - old p| ≤ (accuracy + gap) * g.width := by
  obtain ⟨x, y⟩ := p
  apply g.refineStage_error_of_cell_rows hp
  intro i hi hcell j hj hclose
  have ⟨hx₁, hx₂⟩ := hcell
  let mid := g.midlatitude j
  have hstep := g.longitude_succ i
  have hmono := g.longitude_mono (Nat.le_succ i)
  obtain ⟨hleft, hdleft⟩ := g.rowSample hi hj hcell ⟨le_rfl, hmono⟩ hclose
  obtain ⟨hright, hdright⟩ := g.rowSample hi hj hcell ⟨hmono, le_rfl⟩ hclose
  obtain ⟨hmiddle, hdmiddle⟩ := g.rowSample hi hj hcell hcell hclose
  have hl := haffine _ hleft hdleft
  have hr := haffine _ hright hdright
  have ho := haffine (x, y) hp (by simpa using g.width_pos.le)
  have ha := haccuracy _ hmiddle hdmiddle
  have hb : g.rowSlope target j ≤ a := (hgap mid).trans ha.1
  have habound : a - g.rowSlope target j ≤ accuracy + gap := by
    unfold rowSlope
    dsimp [mid] at ha
    linarith [ha.2, hgap_upper (g.midlatitude j), g.width_pos]
  have hrise : old (g.longitude (i + 1), mid) - old (g.longitude i, mid) = a * g.width := by
    rw [hr, hl]
    dsimp
    rw [hstep]
    ring
  unfold rowRefinement
  change |stripProfile g.left g.width (g.width - g.margin) (g.rowSlope target j) g.columns
      (fun x => old (x, mid)) x - old (x, y)| ≤ _
  rw [stripProfile_eq_cellProfile (sub_nonneg.mpr g.margin_lt_width.le)
    (sub_lt_self _ g.margin_pos) hi hx₁ hx₂]
  change |old (g.longitude i, mid) + cellProfile _ _ _
    (old (g.longitude (i + 1), mid) - old (g.longitude i, mid))
    (x - g.longitude i) - old (x, y)| ≤ _
  rw [hrise, hl, ho]
  have hrewrite : ∀ v : ℝ,
      intercept + a * (g.longitude i, mid).1 + v - (intercept + a * (x, y).1) =
        v - a * (x - g.longitude i) := by intro v; dsimp; ring
  rw [hrewrite]
  refine (cellProfile_affine_error (sub_nonneg.mpr g.margin_lt_width.le)
    (sub_lt_self _ g.margin_pos) hb (sub_nonneg.mpr hx₁) (by linarith)).trans ?_
  exact (mul_le_mul_of_nonneg_left (by linarith [g.margin_pos]) (sub_nonneg.mpr hb)).trans
    (mul_le_mul_of_nonneg_right habound g.width_pos.le)

end

end GlobeFlattening.RectangularMesh
