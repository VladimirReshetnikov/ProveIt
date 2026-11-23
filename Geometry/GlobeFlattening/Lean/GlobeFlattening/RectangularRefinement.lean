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

private theorem dist_le_width {p q : ℝ × ℝ} {width : ℝ}
    (hx : |p.1 - q.1| ≤ width) (hy : |p.2 - q.2| ≤ width) :
    dist p q ≤ width := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le hx hy

/-- Twice the old oscillation over distances of one mesh width bounds the
uniform change. This includes the layers which interpolate two rows. -/
theorem refineStage_uniform_error {old : ℝ × ℝ → ℝ} {target previous : ℝ → ℝ} {osc : ℝ}
    (hold : g.HasLowerSlope old previous)
    (hgap : ∀ y, target y + g.width ≤ previous y)
    (hnonneg : ∀ y ∈ Icc g.bottom (g.latitude (g.transitions + 1)), 0 ≤ target y)
    (hosc : ∀ p ∈ g.rectangle, ∀ q ∈ g.rectangle, dist p q ≤ g.width → |old p - old q| ≤ osc)
    {p : ℝ × ℝ} (hp : p ∈ g.rectangle) :
    |g.refineStage old target p - old p| ≤ 2 * osc := by
  obtain ⟨x, y⟩ := p
  obtain ⟨i, hi, hx₁, hx₂⟩ := exists_mesh_cell (width := g.width) (count := g.columns)
    g.columns_pos hp.1.1 hp.1.2
  change g.longitude i ≤ x at hx₁
  change x ≤ g.longitude (i + 1) at hx₂
  obtain ⟨j₁, j₂, t, h₁, h₂, ht₀, ht₁, hclose₁, hclose₂, hblend⟩ :=
    g.exists_latitude_blend (g.rowRefinement old target) hp.2
  have hrow (j : ℕ) (hj : j ≤ g.transitions) (hclose : |y - g.midlatitude j| ≤ g.width) :
      |g.rowRefinement old target j x - old (x, y)| ≤ 2 * osc := by
    let mid := g.midlatitude j
    have hmid := g.midlatitude_mem hj
    have hleft := g.longitude_mem hi.le
    have hright := g.longitude_mem (Nat.succ_le_of_lt hi)
    have hmono₁ := hold mid hmid (g.longitude i) hleft x hp.1 hx₁
    have hmono₂ := hold mid hmid x hp.1 (g.longitude (i + 1)) hright hx₂
    have hpos : 0 ≤ previous mid := by linarith [hgap mid, hnonneg mid hmid, g.width_pos]
    have hslope : 0 ≤ g.rowSlope target j := add_nonneg (hnonneg _ hmid) g.width_pos.le
    have ha := stripProfile_cell_error (old := fun x => old (x, mid)) (slope := g.rowSlope target j)
      (sub_nonneg.mpr g.margin_lt_width.le) (sub_lt_self _ g.margin_pos) hslope
      (g.cell_rise hold hgap hj) hi hx₁ hx₂
      ((mul_nonneg hpos (sub_nonneg.mpr hx₁)).trans hmono₁ |> sub_nonneg.mp)
      ((mul_nonneg hpos (sub_nonneg.mpr hx₂)).trans hmono₂ |> sub_nonneg.mp)
    have hrise : old (g.longitude (i + 1), mid) - old (g.longitude i, mid) ≤ osc := by
      apply le_trans (le_abs_self _)
      apply hosc _ ⟨hright, hmid⟩ _ ⟨hleft, hmid⟩
      apply dist_le_width
      · have hstep := g.longitude_succ i
        change |g.longitude (i + 1) - g.longitude i| ≤ g.width
        rw [hstep, add_sub_cancel_left, abs_of_nonneg g.width_pos.le]
      · simp [g.width_pos.le]
    have hfreeze : |old (x, mid) - old (x, y)| ≤ osc := by
      apply hosc (x, mid) ⟨hp.1, hmid⟩ (x, y) hp
      apply dist_le_width
      · simp [g.width_pos.le]
      · exact (abs_sub_comm _ _).trans_le hclose
    calc
      _ ≤ |g.rowRefinement old target j x - old (x, mid)| + |old (x, mid) - old (x, y)| :=
        abs_sub_le _ _ _
      _ ≤ osc + osc := add_le_add (ha.trans hrise) hfreeze
      _ = 2 * osc := by ring
  change |latitudeProfile g.layerStart (2 * g.margin) g.transitions
    (g.rowRefinement old target) (x, y) - old (x, y)| ≤ 2 * osc
  rw [hblend x]
  exact latitude_blend_error ht₀ ht₁ (hrow j₁ h₁ hclose₁) (hrow j₂ h₂ hclose₂)


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
  obtain ⟨i, hi, hx₁, hx₂⟩ := exists_mesh_cell (width := g.width) (count := g.columns)
    g.columns_pos hp.1.1 hp.1.2
  change g.longitude i ≤ x at hx₁
  change x ≤ g.longitude (i + 1) at hx₂
  obtain ⟨j₁, j₂, t, h₁, h₂, ht₀, ht₁, hclose₁, hclose₂, hblend⟩ :=
    g.exists_latitude_blend (g.rowRefinement old target) hp.2
  have hrow (j : ℕ) (hj : j ≤ g.transitions) (hclose : |y - g.midlatitude j| ≤ g.width) :
      |g.rowRefinement old target j x - old (x, y)| ≤ (accuracy + gap) * g.width := by
    let mid := g.midlatitude j
    have hmid := g.midlatitude_mem hj
    have hstep := g.longitude_succ i
    have hcloseY : |mid - y| ≤ g.width := (abs_sub_comm _ _).trans_le hclose
    have hcloseL : dist (g.longitude i, mid) (x, y) ≤ g.width :=
      dist_le_width (abs_le.mpr ⟨by linarith, by linarith [g.width_pos]⟩) hcloseY
    have hcloseR : dist (g.longitude (i + 1), mid) (x, y) ≤ g.width :=
      dist_le_width (abs_le.mpr ⟨by linarith [g.width_pos], by linarith⟩) hcloseY
    have hcloseM : dist (x, mid) (x, y) ≤ g.width :=
      dist_le_width (by simp [g.width_pos.le]) hcloseY
    have hl := haffine (g.longitude i, mid) ⟨g.longitude_mem hi.le, hmid⟩ hcloseL
    have hr := haffine (g.longitude (i + 1), mid)
      ⟨g.longitude_mem (Nat.succ_le_of_lt hi), hmid⟩ hcloseR
    have ho := haffine (x, y) hp (by simpa using g.width_pos.le)
    have ha := haccuracy (x, mid) ⟨hp.1, hmid⟩ hcloseM
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
  change |latitudeProfile g.layerStart (2 * g.margin) g.transitions
    (g.rowRefinement old target) (x, y) - old (x, y)| ≤ _
  rw [hblend x]
  exact latitude_blend_error ht₀ ht₁ (hrow j₁ h₁ hclose₁) (hrow j₂ h₂ hclose₂)

end

end GlobeFlattening.RectangularMesh
