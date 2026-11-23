import GlobeFlattening.RectangularMesh
import GlobeFlattening.RefinementLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.UniformSpace.HeineCantor

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

theorem sphereMesh_rectangle : (sphereMesh n θ hθ hθsmall).rectangle = sphereClosedBox := by
  let g := sphereMesh n θ hθ hθsmall
  have hspan : ((n + 1 : ℕ) : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) = Real.pi := by
    field_simp
  have hlon : g.longitude g.columns = Real.pi := by
    change -Real.pi + ((2 * (n + 1) : ℕ) : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) = _
    rw [Nat.cast_mul, mul_assoc, hspan]
    push_cast
    ring
  have hlat : g.latitude (g.transitions + 1) = Real.pi / 2 := by
    change -(Real.pi / 2) + ((n + 1 : ℕ) : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) = _
    rw [hspan]
    ring
  change g.rectangle = sphereClosedBox
  rw [RectangularMesh.rectangle, hlon, hlat]
  rfl

theorem sphereMesh_area_factor :
    ((sphereMesh n θ hθ hθsmall).columns : ℝ) *
      ((sphereMesh n θ hθ hθsmall).transitions + 1 : ℕ) *
      (sphereMesh n θ hθ hθsmall).width^2 = 2 * Real.pi^2 := by
  change ((2 * (n + 1) : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
    (Real.pi / ((n + 1 : ℕ) : ℝ))^2 = _
  rw [Nat.cast_mul, Nat.cast_ofNat]
  field_simp

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
  simpa only [stageTarget, add_sub_add_right_eq_sub] using Real.abs_cos_sub_cos_le y z

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
    Tendsto (fun n : ℕ => c / (4 : ℝ)^n) atTop (𝓝 0) :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).const_div_atTop c

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
  let osc := previousRadius / 4 / (2 : ℝ)^k
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_sphereClosedBox.uniformContinuousOn_of_continuous hf) osc (by unfold osc; positivity)
  let cap := min r (min (3 * δ / (4 : ℝ)^(k + 1)) (previousRadius / 4))
  have hcap : 0 < cap := lt_min hr (lt_min (by positivity) (by positivity))
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.pi / cap)
  have hNpos : (0 : ℝ) < N := (div_pos Real.pi_pos hcap).trans hN
  have hwidth : Real.pi / (N : ℝ) < cap := by
    rw [div_lt_iff₀ hNpos, mul_comm]
    exact (div_lt_iff₀ hcap).mp hN
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by exact_mod_cast hNpos.ne')
  let g := sphereMesh m theta (stageMargin_pos _) (stageMargin_le_eighth _)
  have hgrect : g.rectangle = sphereClosedBox := sphereMesh_rectangle _ _ _ _
  have hmargin : g.margin = theta * g.width := rfl
  have htrim : 4 * g.margin ≤ g.width := by
    rw [hmargin]
    have htheta : 4 * theta ≤ 1 := by linarith [stageMargin_le_eighth (k + 1)]
    nlinarith [mul_le_mul_of_nonneg_right htheta g.width_pos.le]
  have hscale : g.width ≤ 3 * δ / (4 : ℝ)^(k + 1) :=
    hwidth.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hwidth' : g.width ≤ previousRadius / 4 :=
    hwidth.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨g, hgrect, hmargin, ?_, htrim, sphereMesh_area_factor _ _ _ _,
    hscale, hwidth', by linarith [g.margin_lt_width], ?_⟩
  · rw [hmargin, mul_div_cancel_right₀ _ g.width_pos.ne']
  · intro p hp q hq hdist
    rw [hgrect] at hp hq
    rw [← Real.dist_eq]
    exact (hmod p hp q hq (hdist.trans_lt (hwidth.trans_le (min_le_left _ _)))).le

/-- The loss fraction of a trimmed mesh is bounded by the dyadic budget,
leaving a common budget that also covers the initial rectangle. -/
theorem seven_stageMargin_le_dyadic (n : ℕ) :
    7 * stageMargin n ≤ ((2 : ℝ)⁻¹)^n := by
  calc
    _ = (7 / 8) * ((2 : ℝ)⁻¹)^n := by
      unfold stageMargin
      rw [pow_add, inv_pow]
      field_simp; ring
    _ ≤ _ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show (7 : ℝ) / 8 ≤ 1 by norm_num) (by positivity :
          0 ≤ ((2 : ℝ)⁻¹)^n)

/-- The bad areas have finite sum whenever they are under the common
dyadic budget. -/
theorem sphereMesh_bad_area_summable {bad : ℕ → ℝ≥0∞}
    (hbad : ∀ n, bad n ≤ ENNReal.ofReal ((2 * Real.pi^2) * ((2 : ℝ)⁻¹)^n)) :
    (∑' n, bad n) ≠ ∞ := by
  have hnonneg : 0 ≤ 2 * Real.pi^2 := by positivity
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp : (2 : ℝ≥0∞) ≠ ∞))
  calc
    (∑' n, bad n) ≤ ∑' n : ℕ, ENNReal.ofReal (2 * Real.pi^2) * ((2 : ℝ≥0∞)⁻¹)^n := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [ENNReal.ofReal_mul hnonneg,
        ENNReal.ofReal_pow (by positivity : 0 ≤ (2 : ℝ)⁻¹),
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat] using hbad n
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]

end

end GlobeFlattening
