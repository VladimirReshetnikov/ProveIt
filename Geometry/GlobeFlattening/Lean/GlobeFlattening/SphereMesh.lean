import GlobeFlattening.RectangularMesh
import GlobeFlattening.RefinementLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Mesh and slope schedule for the sphere's coordinate rectangle

The latitude interval has length π and the longitude interval has length 2π.
With `n + 1` rows, the same spacing closes up both grids exactly.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GlobeFlattening

noncomputable section

/-- The closed longitude-latitude coordinate rectangle of the report. -/
def sphereClosedBox : Set (ℝ × ℝ) :=
  Icc (-Real.pi) Real.pi ×ˢ Icc (-(Real.pi / 2)) (Real.pi / 2)

theorem isCompact_sphereClosedBox : IsCompact sphereClosedBox :=
  isCompact_Icc.prod isCompact_Icc

theorem volume_sphereClosedBox : volume sphereClosedBox = ENNReal.ofReal (2 * Real.pi^2) := by
  rw [sphereClosedBox, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith [Real.pi_pos])]
  congr 1
  ring

/-- Equal spacing in both coordinates, with `n + 1` rows and twice as many columns. -/
def sphereMesh (n : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ ≤ 1 / 8) :
    RectangularMesh where
  left := -Real.pi
  bottom := -(Real.pi / 2)
  width := Real.pi / ((n + 1 : ℕ) : ℝ)
  margin := θ * (Real.pi / ((n + 1 : ℕ) : ℝ))
  columns := 2 * (n + 1)
  transitions := n
  columns_pos := by omega
  margin_pos := by positivity
  layer_small := by
    have ht : 2 * θ < 1 := by linarith
    have hw : 0 < Real.pi / ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith [mul_lt_mul_of_pos_right ht hw]

variable (n : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ ≤ 1 / 8)

@[simp] theorem sphereMesh_width :
    (sphereMesh n θ hθ hθsmall).width = Real.pi / ((n + 1 : ℕ) : ℝ) := rfl

theorem sphereMesh_margin :
    (sphereMesh n θ hθ hθsmall).margin = θ * (sphereMesh n θ hθ hθsmall).width := rfl

@[simp] theorem sphereMesh_left : (sphereMesh n θ hθ hθsmall).left = -Real.pi := rfl

@[simp] theorem sphereMesh_bottom : (sphereMesh n θ hθ hθsmall).bottom = -(Real.pi / 2) := rfl

@[simp] theorem sphereMesh_columns : (sphereMesh n θ hθ hθsmall).columns = 2 * (n + 1) := rfl

@[simp] theorem sphereMesh_transitions : (sphereMesh n θ hθ hθsmall).transitions = n := rfl

theorem sphereMesh_margin_div_width :
    (sphereMesh n θ hθ hθsmall).margin / (sphereMesh n θ hθ hθsmall).width = θ := by
  rw [sphereMesh_margin, mul_div_cancel_right₀ _ (sphereMesh n θ hθ hθsmall).width_pos.ne']

theorem sphereMesh_trim_small :
    4 * (sphereMesh n θ hθ hθsmall).margin ≤ (sphereMesh n θ hθ hθsmall).width := by
  rw [sphereMesh_margin]
  have ht : 4 * θ ≤ 1 := by linarith
  have hw := (sphereMesh n θ hθ hθsmall).width_pos.le
  nlinarith [mul_le_mul_of_nonneg_right ht hw]

theorem sphereMesh_longitude_right :
    (sphereMesh n θ hθ hθsmall).longitude (sphereMesh n θ hθ hθsmall).columns = Real.pi := by
  unfold RectangularMesh.longitude meshPoint
  simp only [sphereMesh_left, sphereMesh_columns, sphereMesh_width, Nat.cast_mul,
    Nat.cast_ofNat]
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

theorem sphereMesh_latitude_top :
    (sphereMesh n θ hθ hθsmall).latitude ((sphereMesh n θ hθ hθsmall).transitions + 1) =
      Real.pi / 2 := by
  unfold RectangularMesh.latitude meshPoint
  simp only [sphereMesh_bottom, sphereMesh_transitions, sphereMesh_width]
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

@[simp] theorem sphereMesh_rectangle : (sphereMesh n θ hθ hθsmall).rectangle = sphereClosedBox := by
  rw [RectangularMesh.rectangle, sphereMesh_longitude_right, sphereMesh_latitude_top,
    sphereMesh_left, sphereMesh_bottom, sphereClosedBox]

theorem sphereMesh_area_factor :
    ((sphereMesh n θ hθ hθsmall).columns : ℝ) *
      ((sphereMesh n θ hθ hθsmall).transitions + 1 : ℕ) *
      (sphereMesh n θ hθ hθsmall).width^2 = 2 * Real.pi^2 := by
  simp only [sphereMesh_columns, sphereMesh_transitions, sphereMesh_width, Nat.cast_mul,
    Nat.cast_ofNat]
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

omit n in
/-- The sphere mesh can meet a positive width cap and an oscillation budget
on the old profile simultaneously. -/
theorem exists_sphereMesh {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f sphereClosedBox)
    {cap oscillation : ℝ} (hcap : 0 < cap) (hosc : 0 < oscillation) :
    ∃ n : ℕ, let g := sphereMesh n θ hθ hθsmall
      g.width ≤ cap ∧ ∀ p ∈ g.rectangle, ∀ q ∈ g.rectangle, dist p q ≤ g.width →
        |f p - f q| ≤ oscillation := by
  obtain ⟨N, hN, _, hwidth, hmod⟩ :=
    exists_refinement_mesh isCompact_sphereClosedBox hf Real.pi_pos hcap hosc
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  refine ⟨n, hwidth, ?_⟩
  intro p hp q hq hpq
  rw [sphereMesh_rectangle] at hp hq
  exact (Real.dist_eq (f p) (f q)) ▸ hmod p hp q hq hpq

/-- Relative margin θₙ, reserving the same proportion at every edge of each
cell of a given stage. Stage zero has this value too, though it uses no mesh. -/
def stageMargin (n : ℕ) : ℝ := 1 / (2 : ℝ)^(n + 3)

theorem stageMargin_pos (n : ℕ) : 0 < stageMargin n := by unfold stageMargin; positivity

theorem stageMargin_le_eighth (n : ℕ) : stageMargin n ≤ 1 / 8 := by
  unfold stageMargin
  rw [pow_add]
  have hpow : 1 ≤ (2 : ℝ)^n := one_le_pow₀ (by norm_num)
  apply div_le_div_of_nonneg_left (by norm_num)
  · norm_num
  · nlinarith

theorem stageMargin_tendsto_zero : Tendsto stageMargin atTop (𝓝 0) :=
  (tendsto_dyadic_ratio_zero 1).comp (tendsto_add_atTop_nat 3)

/-- Scheduled lower slope γₙ. The positive reserve drops by a factor of four
at each successive stage. -/
def stageTarget (δ : ℝ) (n : ℕ) (y : ℝ) : ℝ := Real.cos y + δ / (4 : ℝ)^n

@[simp] theorem stageTarget_zero (δ y : ℝ) : stageTarget δ 0 y = Real.cos y + δ := by
  simp [stageTarget]

theorem stageTarget_nonneg (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) {y : ℝ}
    (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) : 0 ≤ stageTarget δ n y :=
  add_nonneg (Real.cos_nonneg_of_mem_Icc hy) (div_nonneg hδ (by positivity))

theorem stageTarget_variation (δ : ℝ) (n : ℕ) (y z : ℝ) :
    |stageTarget δ n y - stageTarget δ n z| ≤ |y - z| := by
  have h : stageTarget δ n y - stageTarget δ n z = Real.cos y - Real.cos z := by
    unfold stageTarget
    ring
  rw [h]
  exact Real.abs_cos_sub_cos_le y z

theorem stageTarget_difference (δ : ℝ) (n : ℕ) (y : ℝ) :
    stageTarget δ n y = stageTarget δ (n + 1) y + 3 * δ / (4 : ℝ)^(n + 1) := by
  unfold stageTarget
  rw [pow_succ]
  field_simp
  ring

theorem stageTarget_gap {δ width : ℝ} {n : ℕ}
    (hwidth : width ≤ 3 * δ / (4 : ℝ)^(n + 1)) (y : ℝ) :
    stageTarget δ (n + 1) y + width ≤ stageTarget δ n y := by
  rw [stageTarget_difference δ n y]
  exact add_le_add le_rfl hwidth

theorem tendsto_quarter_ratio_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c / (4 : ℝ)^n) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ((4 : ℝ)⁻¹)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa [div_eq_mul_inv, inv_pow] using hpow.const_mul c

theorem stageTarget_tendsto (δ y : ℝ) :
    Tendsto (fun n => stageTarget δ n y) atTop (𝓝 (Real.cos y)) := by
  simpa only [stageTarget, add_zero] using (tendsto_quarter_ratio_zero δ).const_add (Real.cos y)

/-- All numerical requirements when choosing the next mesh, including the
oscillation budget whose double is the global step bound. -/
theorem exists_scheduledSphereMesh {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f sphereClosedBox)
    {δ previousRadius : ℝ} (hδ : 0 < δ) (hprevious : 0 < previousRadius) (k : ℕ) :
    ∃ g : RectangularMesh,
      g.rectangle = sphereClosedBox ∧
      g.margin = stageMargin (k + 1) * g.width ∧
      g.margin / g.width = stageMargin (k + 1) ∧
      4 * g.margin ≤ g.width ∧
      (g.columns : ℝ) * (g.transitions + 1 : ℕ) * g.width^2 = 2 * Real.pi^2 ∧
      g.width ≤ 3 * δ / (4 : ℝ)^(k + 1) ∧
      g.width ≤ previousRadius / 4 ∧
      g.margin ≤ previousRadius / 2 ∧
      ∀ p ∈ g.rectangle, ∀ q ∈ g.rectangle, dist p q ≤ g.width →
        |f p - f q| ≤ previousRadius / 4 / (2 : ℝ)^k := by
  let theta := stageMargin (k + 1)
  have htheta : 0 < theta := stageMargin_pos _
  have htheta_small : theta ≤ 1 / 8 := stageMargin_le_eighth _
  obtain ⟨m, hm, hmod⟩ := exists_sphereMesh theta htheta htheta_small hf
    (cap := min (3 * δ / (4 : ℝ)^(k + 1)) (previousRadius / 4)) (by positivity)
    (oscillation := previousRadius / 4 / (2 : ℝ)^k) (by positivity)
  let g := sphereMesh m theta htheta htheta_small
  have hwidth : g.width ≤ previousRadius / 4 := hm.trans (min_le_right _ _)
  have hhalf : g.margin ≤ previousRadius / 2 := by
    linarith [g.margin_lt_width]
  exact ⟨g, sphereMesh_rectangle _ _ _ _, sphereMesh_margin _ _ _ _,
    sphereMesh_margin_div_width _ _ _ _, sphereMesh_trim_small _ _ _ _,
    sphereMesh_area_factor _ _ _ _, hm.trans (min_le_left _ _), hwidth, hhalf, hmod⟩

theorem stageMargin_le_geometric (n : ℕ) :
    stageMargin n ≤ ((2 : ℝ)⁻¹)^n := by
  calc
    stageMargin n = (1 / 8) * ((2 : ℝ)⁻¹)^n := by
      unfold stageMargin
      rw [pow_add, inv_pow]
      field_simp; ring
    _ ≤ _ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show (1 : ℝ) / 8 ≤ 1 by norm_num) (by positivity :
          0 ≤ ((2 : ℝ)⁻¹)^n)

/-- Every positive-stage loss is bounded by a geometric term. The initial
stage has no trimmed tiles, so it only needs a finite loss. -/
theorem sphereMesh_bad_area_summable {bad : ℕ → ℝ≥0∞}
    (hzero : bad 0 ≠ ∞)
    (hbad : ∀ n, bad (n + 1) ≤
      ENNReal.ofReal (7 * stageMargin (n + 1) * (2 * Real.pi^2))) :
    (∑' n, bad n) ≠ ∞ := by
  let C : ℝ≥0∞ := max (bad 0) (ENNReal.ofReal (7 * (2 * Real.pi^2)))
  have hC : C ≠ ∞ :=
    ne_of_lt (max_lt (lt_top_iff_ne_top.mpr hzero) ENNReal.ofReal_lt_top)
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (by simp : (2 : ℝ≥0∞) ≠ ∞))
  calc
    (∑' n, bad n) ≤ ∑' n : ℕ, C * ((2 : ℝ≥0∞)⁻¹)^n := by
      apply ENNReal.tsum_le_tsum
      intro n
      cases n with
      | zero => simpa only [pow_zero, mul_one] using (le_max_left (bad 0) _)
      | succ n =>
          have hnonneg : 0 ≤ 7 * (2 * Real.pi^2) := by positivity
          calc
            _ ≤ ENNReal.ofReal (7 * stageMargin (n + 1) * (2 * Real.pi^2)) := hbad n
            _ ≤ ENNReal.ofReal ((7 * (2 * Real.pi^2)) * ((2 : ℝ)⁻¹)^(n + 1)) := by
              apply ENNReal.ofReal_le_ofReal
              rw [show 7 * stageMargin (n + 1) * (2 * Real.pi^2) =
                (7 * (2 * Real.pi^2)) * stageMargin (n + 1) by ring]
              exact mul_le_mul_of_nonneg_left (stageMargin_le_geometric _) hnonneg
            _ = ENNReal.ofReal (7 * (2 * Real.pi^2)) * ((2 : ℝ≥0∞)⁻¹)^(n + 1) := by
              rw [ENNReal.ofReal_mul hnonneg, ENNReal.ofReal_pow (by positivity),
                ENNReal.ofReal_inv_of_pos (by norm_num)]
              simp
            _ ≤ _ := mul_le_mul' (le_max_right _ _) le_rfl
    _ = C * 2 := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]

end

end GlobeFlattening
