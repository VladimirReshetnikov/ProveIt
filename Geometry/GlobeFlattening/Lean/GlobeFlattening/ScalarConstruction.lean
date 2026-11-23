import GlobeFlattening.CoordinateRectangles
import GlobeFlattening.SingularSeries
import GlobeFlattening.SingularStaircase
import GlobeFlattening.StaircaseEstimates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The scalar longitude coordinate from singular staircases

Approximate longitude by monotone singular staircases `X n` and rescale
them for latitude as `Y n`. The correction weights are successive drops
of `rate n + cos (Y n y)`. Their positivity gives the strict lower
longitude slope.

The scalar coordinate sums increments of `X` weighted by
`rate n + cos (Y n y)`. On the chart, telescoping the product differences
expresses it as the sinusoidal coordinate plus the longitude correction.
The two expressions bound horizontal and vertical errors by a single
monotone singular sum and its latitude rescaling.
-/

namespace GlobeFlattening

open Filter Set MeasureTheory
open scoped NNReal Topology

noncomputable section

abbrev longitude (x : ℝ) : ℝ :=
  (projIcc (-Real.pi) Real.pi (neg_le_self Real.pi_pos.le) x).1

theorem longitude_of_mem {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) : longitude x = x :=
  congrArg Subtype.val (projIcc_of_mem _ hx)

private theorem double_latitude_mem {y : ℝ} (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    2 * y ∈ Icc (-Real.pi) Real.pi :=
  ⟨by linarith only [hy.1], by linarith only [hy.2]⟩

def rate (δ : ℝ) (n : ℕ) := δ * (1 / 2 : ℝ)^n

private theorem rate_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < rate δ n := by
  unfold rate
  positivity

theorem rate_succ (δ : ℝ) (n : ℕ) : rate δ (n + 1) = rate δ n / 2 := by
  simp only [rate, pow_succ]; ring

theorem hasSum_rate (δ : ℝ) : HasSum (rate δ) (δ * 2) := hasSum_geometric_two.mul_left δ

theorem summable_rate (δ : ℝ) : Summable (rate δ) := (hasSum_rate δ).summable

structure Staircases (δ : ℝ) where
  delta_pos : 0 < δ
  X : ℕ → ℝ → ℝ
  monoX : ∀ n, Monotone (X n)
  continuousX : ∀ n, Continuous (X n)
  singularX : ∀ n, ∀ᵐ x ∂volume, HasDerivAt (X n) 0 x
  boundX : ∀ n x, |X n x| ≤ Real.pi
  errorX : ∀ n x, |X n x - longitude x| ≤ min (rate δ n / 4) (1 / 4)

theorem exists_staircases {δ : ℝ} (hδ : 0 < δ) : Nonempty (Staircases δ) := by
  have hX (n : ℕ) := exists_singular_approx (neg_lt_self Real.pi_pos)
    (lt_min (div_pos (rate_pos hδ n) (by norm_num : (0 : ℝ) < 4))
      (by norm_num : (0 : ℝ) < 1 / 4))
  choose X hc hm hr he hd using hX
  exact ⟨⟨hδ, X, hm, hc, hd, fun n x => abs_le.mpr (hr n x), he⟩⟩

namespace Staircases

variable {δ : ℝ} (S : Staircases δ)

theorem errorRateX (n : ℕ) (x : ℝ) : |S.X n x - longitude x| ≤ rate δ n / 4 :=
  (S.errorX n x).trans (min_le_left _ _)

private theorem X_step_bound (n : ℕ) (x : ℝ) : |S.X (n + 1) x - S.X n x| ≤ rate δ (n + 1) := by
  have h := abs_sub_le (S.X (n + 1) x) (longitude x) (S.X n x)
  rw [abs_sub_comm (longitude x)] at h
  have hnext := S.errorRateX (n + 1) x
  rw [rate_succ] at hnext ⊢
  linarith only [h, hnext, S.errorRateX n x, (rate_pos S.delta_pos n).le]

theorem tendsto_X {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    Tendsto (fun n => S.X n x) atTop (𝓝 x) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (g := fun n => rate δ n / 4) (fun _ => norm_nonneg _) (fun n => ?_) ?_
  · simpa only [longitude_of_mem hx, Real.norm_eq_abs] using S.errorRateX n x
  · simpa only [zero_div] using (summable_rate δ).tendsto_atTop_zero.div_const 4

private def latitudeWeight (δ : ℝ) (n : ℕ) (t : ℝ) := rate δ n + Real.cos (t / 2)

def latitudeProfile (n : ℕ) (y : ℝ) : ℝ := latitudeWeight δ n (S.X n (2 * y))
def coefficient (n : ℕ) (y : ℝ) : ℝ := S.latitudeProfile n y - S.latitudeProfile (n + 1) y

private theorem abs_latitudeWeight_le (S : Staircases δ) (n : ℕ) (t : ℝ) :
    |latitudeWeight δ n t| ≤ δ + 1 := by
  refine (abs_add_le _ _).trans (add_le_add ?_ (Real.abs_cos_le_one _))
  rw [abs_of_pos (rate_pos S.delta_pos n)]
  exact mul_le_of_le_one_right S.delta_pos.le (pow_le_one₀ (by norm_num) (by norm_num))

theorem tendsto_latitudeProfile {y : ℝ} (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    Tendsto (fun n => S.latitudeProfile n y) atTop (𝓝 (Real.cos y)) := by
  have hY := (S.tendsto_X (double_latitude_mem hy)).div_const 2
  rw [mul_div_cancel_left₀ _ two_ne_zero] at hY
  simpa only [latitudeProfile, latitudeWeight, Function.comp_def, zero_add] using
    (summable_rate δ).tendsto_atTop_zero.add ((Real.continuous_cos.tendsto y).comp hY)

private theorem abs_cos_half_sub_le (x y : ℝ) :
    |Real.cos (x / 2) - Real.cos (y / 2)| ≤ |x - y| / 2 := by
  have hcos : LipschitzWith 1 Real.cos :=
    lipschitzWith_of_nnnorm_deriv_le Real.differentiable_cos <| by simpa using! Real.abs_sin_le_one
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, ← sub_div,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hcos.dist_le_mul (x / 2) (y / 2)

theorem coefficient_bounds (n : ℕ) (y : ℝ) :
    0 < S.coefficient n y ∧ |S.coefficient n y| ≤ rate δ n := by
  have hcos := abs_le.mp <| (abs_cos_half_sub_le _ _).trans
    (div_le_div_of_nonneg_right (S.X_step_bound n (2 * y)) (by norm_num : 0 ≤ (2 : ℝ)))
  unfold coefficient latitudeProfile latitudeWeight
  rw [rate_succ] at hcos ⊢
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    linarith only [hcos.1, hcos.2, rate_pos S.delta_pos n]

def correction (p : ℝ × ℝ) := ∑' n, S.coefficient n p.2 * S.X n p.1

private theorem summable_centered_correction (p : ℝ × ℝ) (z : ℝ) :
    Summable (fun n => S.coefficient n p.2 * (S.X n p.1 - z)) :=
  ((summable_rate δ).mul_right (Real.pi + |z|)).of_norm_bounded fun n =>
    norm_mul_le_of_le (S.coefficient_bounds n p.2).2 (by
      simpa only [Real.norm_eq_abs] using (abs_sub (S.X n p.1) z).trans
        (add_le_add (S.boundX n p.1) le_rfl))

theorem summable_correction (p : ℝ × ℝ) : Summable (fun n => S.coefficient n p.2 * S.X n p.1) := by
  simpa only [sub_zero] using S.summable_centered_correction p 0

def longitudeIncrement : ℕ → ℝ → ℝ
  | 0 => S.X 0
  | n + 1 => fun x => S.X (n + 1) x - S.X n x

private theorem rate_le_rate_add_pi (δ : ℝ) (n : ℕ) : rate δ n ≤ rate (δ + Real.pi) n :=
  mul_le_mul_of_nonneg_right (le_add_of_nonneg_right Real.pi_pos.le) (by positivity)

theorem longitudeIncrement_bound (n : ℕ) (x : ℝ) :
    |S.longitudeIncrement n x| ≤ rate (δ + Real.pi) n := by
  cases n with
  | zero => simpa [longitudeIncrement, rate] using
      (S.boundX 0 x).trans (le_add_of_nonneg_left S.delta_pos.le)
  | succ n =>
    exact (S.X_step_bound n x).trans (rate_le_rate_add_pi δ _)

def incrementTerm (n : ℕ) (p : ℝ × ℝ) :=
  S.longitudeIncrement n p.1 * S.latitudeProfile n p.2

def scalar (p : ℝ × ℝ) := ∑' n, S.incrementTerm n p

private theorem scalar_series :
    (∀ p, HasSum (fun n => S.incrementTerm n p) (S.scalar p)) ∧ Continuous S.scalar := by
  have huniform := tendstoUniformly_tsum (f := S.incrementTerm)
    ((summable_rate (δ + Real.pi)).mul_right (δ + 1)) fun n p =>
      norm_mul_le_of_le (S.longitudeIncrement_bound n p.1) (S.abs_latitudeWeight_le n (S.X n (2 * p.2)))
  refine ⟨huniform.tendsto_at, huniform.continuous (Frequently.of_forall fun t =>
    continuous_finsetSum t fun n _ => ?_)⟩
  have hinc : Continuous (S.longitudeIncrement n) := by
    cases n with
    | zero => exact S.continuousX 0
    | succ n => exact (S.continuousX (n + 1)).sub (S.continuousX n)
  have hprofile : Continuous (S.latitudeProfile n) := by
    have hX := S.continuousX n
    fun_prop [latitudeProfile, latitudeWeight]
  exact (hinc.comp continuous_fst).mul (hprofile.comp continuous_snd)

private theorem scalar_sub_eq_centered_correction {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) (z : ℝ) :
    S.scalar p - z * S.latitudeProfile 0 p.2 =
      (p.1 - z) * Real.cos p.2 + ∑' n, S.coefficient n p.2 * (S.X n p.1 - z) := by
  have hsum := (S.scalar_series.1 p).summable
  rw [scalar, hsum.tsum_eq_zero_add, mul_comm (p.1 - z) (Real.cos p.2)]
  exact tsum_weighted_increment_centered (S.summable_centered_correction p z)
    ((summable_nat_add_iff 1).2 hsum)
    ((S.tendsto_latitudeProfile hp.2).mul ((S.tendsto_X hp.1).sub_const z))

theorem scalar_eq_correction {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) :
    S.scalar p = p.1 * Real.cos p.2 + S.correction p := by
  simpa only [zero_mul, sub_zero, correction] using S.scalar_sub_eq_centered_correction hp 0

theorem scalar_strictLowerSlope : StrictLowerSlopeOn S.scalar Real.cos sphereClosedBox := by
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq rfl hxx'
  obtain ⟨n, hX⟩ := ((S.tendsto_X hp.1).eventually_lt (S.tendsto_X hq.1) hxx').exists
  have hsum : S.correction (x, y) < S.correction (x', y) :=
    Summable.tsum_lt_tsum
      (fun k => mul_le_mul_of_nonneg_left (S.monoX k hxx'.le) (S.coefficient_bounds k y).1.le)
      (mul_lt_mul_of_pos_left hX (S.coefficient_bounds n y).1)
      (S.summable_correction (x, y)) (S.summable_correction (x', y))
  rw [S.scalar_eq_correction hp, S.scalar_eq_correction hq]
  nlinarith only [hsum]

theorem scalar_error {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) :
    |S.scalar p - (Real.cos p.2 + δ) * p.1| ≤ δ := by
  have hcor : |S.scalar p - S.latitudeProfile 0 p.2 * p.1| ≤ δ / 2 := by
    rw [mul_comm (S.latitudeProfile 0 p.2), S.scalar_sub_eq_centered_correction hp,
      sub_self, zero_mul, zero_add, ← Real.norm_eq_abs]
    have hrate := (hasSum_rate δ).mul_right (1 / 4 : ℝ)
    rw [show δ * 2 * (1 / 4) = δ / 2 by ring] at hrate
    refine tsum_of_norm_bounded hrate fun n => ?_
    exact norm_mul_le_of_le (S.coefficient_bounds n p.2).2 (by
      simpa only [Real.norm_eq_abs, longitude_of_mem hp.1] using
        (S.errorX n p.1).trans (min_le_right _ _))
  have hlat : |S.latitudeProfile 0 p.2 * p.1 - (Real.cos p.2 + δ) * p.1| ≤ δ / 2 := by
    have hprofile : |S.latitudeProfile 0 p.2 - (Real.cos p.2 + δ)| ≤ δ / 8 := by
      have hX := S.errorRateX 0 (2 * p.2)
      rw [longitude_of_mem (double_latitude_mem hp.2), rate, pow_zero, mul_one] at hX
      have hcos := abs_cos_half_sub_le (S.X 0 (2 * p.2)) (2 * p.2)
      rw [mul_div_cancel_left₀ p.2 two_ne_zero] at hcos
      simpa only [latitudeProfile, latitudeWeight, rate, pow_zero, mul_one, add_comm (Real.cos p.2) δ,
        add_sub_add_left_eq_sub] using hcos.trans (show _ ≤ δ / 8 by linarith only [hX])
    rw [← sub_mul, ← Real.norm_eq_abs]
    refine (norm_mul_le_of_le hprofile (abs_le.mpr hp.1)).trans ?_
    nlinarith only [mul_nonneg S.delta_pos.le (sub_nonneg.mpr Real.pi_le_four)]
  exact (abs_sub_le ..).trans (by linarith only [hcor, hlat])

def horizontalControl (x : ℝ) := ∑' n, rate (δ + Real.pi) n * S.X n x

theorem linearization_bound (hcontrol : ∀ t, Summable (fun n => rate (δ + Real.pi) n * S.X n t))
    {p q : ℝ × ℝ} (hp : p ∈ sphereClosedBox) (hq : q ∈ sphereClosedBox) :
    |S.scalar q - S.scalar p - Real.cos p.2 * (q.1 - p.1)| ≤
      |S.horizontalControl q.1 - S.horizontalControl p.1| +
        |S.horizontalControl (2 * q.2) - S.horizontalControl (2 * p.2)| := by
  let mid := (q.1, p.2)
  calc
    _ = |(S.correction mid - S.correction p) + (S.scalar q - S.scalar mid)| := by
      rw [S.scalar_eq_correction hp, S.scalar_eq_correction (p := mid) ⟨hq.1, hp.2⟩]
      simp only [mid]
      congr 1
      ring
    _ ≤ _ := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · exact abs_tsum_weighted_comp_sub_le (X := S.X) (f := fun _ => id) hcontrol
          (fun n => (S.coefficient_bounds n p.2).2.trans (rate_le_rate_add_pi δ n)) S.monoX
          (fun _ _ _ => le_rfl) p.1 q.1 (S.summable_correction p) (S.summable_correction mid)
      · refine abs_tsum_weighted_comp_sub_le (X := S.X) (f := latitudeWeight δ) hcontrol
          (fun n => S.longitudeIncrement_bound n q.1) S.monoX
          (fun n x y => ?_) (2 * p.2) (2 * q.2) (S.scalar_series.1 mid).summable (S.scalar_series.1 q).summable
        simpa only [latitudeWeight, add_sub_add_left_eq_sub] using
          (abs_cos_half_sub_le y x).trans (half_le_self (abs_nonneg _))

end Staircases

/-- A close approximation to the sinusoidal longitude coordinate with the
prescribed horizontal differential almost everywhere and increasing rows. -/
theorem exists_strict_scalar_flattening {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℝ × ℝ → ℝ, ∃ E : Set (ℝ × ℝ),
      ContinuousOn u sphereClosedBox ∧ MeasurableSet E ∧ E ⊆ sphereLongitudeDomain ∧
      volume (sphereLongitudeDomain \ E) = 0 ∧
      (∀ q ∈ sphereClosedBox, |u q - (Real.cos q.2 + δ) * q.1| ≤ δ) ∧
      StrictLowerSlopeOn u Real.cos sphereClosedBox ∧
      ∀ p ∈ E, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  obtain ⟨S⟩ := exists_staircases hδ
  obtain ⟨hcontrol, hsingular⟩ := summable_and_singular_weighted_tsum S.X (rate (δ + Real.pi))
    (fun n => (rate_pos (add_pos hδ Real.pi_pos) n).le)
    (summable_rate (δ + Real.pi)) S.boundX S.continuousX S.monoX S.singularX
  obtain ⟨E, hm, hsub, hnull, hderiv⟩ :=
    exists_scaled_product_derivative_good S.horizontalControl (c := 2) (by norm_num) sphereLongitudeDomain
      isOpen_sphereLongitudeDomain.measurableSet hsingular
  refine ⟨S.scalar, E, S.scalar_series.2.continuousOn, hm, hsub, hnull, fun _ => S.scalar_error,
    S.scalar_strictLowerSlope, ?_⟩
  intro p hp
  have hd := hderiv p hp
  apply hasFDerivAt_of_increment_bounds (L := ContinuousLinearMap.fst ℝ ℝ ℝ)
    (M := (2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) hd.1 hd.2
  filter_upwards [isOpen_sphereLongitudeDomain.mem_nhds (hsub hp)] with q hq
  exact S.linearization_bound hcontrol (sphereLongitudeDomain_subset_box (hsub hp))
    (sphereLongitudeDomain_subset_box hq)

end
end GlobeFlattening
