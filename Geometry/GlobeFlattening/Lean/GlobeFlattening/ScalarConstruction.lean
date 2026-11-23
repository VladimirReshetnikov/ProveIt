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
  errorX : ∀ n x, |X n x - longitude x| ≤ min (rate δ n / 4) (min (1 / 4) (δ / Real.pi))

theorem exists_staircases {δ : ℝ} (hδ : 0 < δ) : Nonempty (Staircases δ) := by
  have hX (n : ℕ) := exists_singular_approx (neg_lt_self Real.pi_pos)
    (lt_min (div_pos (rate_pos hδ n) (by norm_num : (0 : ℝ) < 4))
      (lt_min (by norm_num : (0 : ℝ) < 1 / 4) (div_pos hδ Real.pi_pos)))
  choose X hc hm hr he hd using hX
  exact ⟨⟨hδ, X, hm, hc, hd, fun n x => abs_le.mpr (hr n x), he⟩⟩

namespace Staircases

variable {δ : ℝ} (S : Staircases δ)

theorem errorRateX (n : ℕ) (x : ℝ) : |S.X n x - longitude x| ≤ rate δ n / 4 :=
  (S.errorX n x).trans (min_le_left _ _)

theorem rate_nonneg (S : Staircases δ) (n : ℕ) : 0 ≤ rate δ n := (rate_pos S.delta_pos n).le

private theorem X_step_bound (n : ℕ) (x : ℝ) : |S.X n x - S.X (n + 1) x| ≤ rate δ (n + 1) := by
  calc
    _ ≤ |S.X n x - longitude x| + |longitude x - S.X (n + 1) x| := abs_sub_le ..
    _ ≤ rate δ n / 4 + rate δ (n + 1) / 4 := by
      rw [abs_sub_comm (longitude x)]
      exact add_le_add (S.errorRateX _ _) (S.errorRateX _ _)
    _ ≤ _ := by rw [rate_succ]; linarith only [S.rate_nonneg n]

theorem abs_rate_le (S : Staircases δ) (n : ℕ) : |rate δ n| ≤ δ := by
  rw [abs_of_nonneg (S.rate_nonneg n)]
  exact mul_le_of_le_one_right S.delta_pos.le (pow_le_one₀ (by norm_num) (by norm_num))

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
    |latitudeWeight δ n t| ≤ δ + 1 :=
  (abs_add_le _ _).trans (add_le_add (S.abs_rate_le n) (Real.abs_cos_le_one _))

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

private theorem lipschitzWith_latitudeWeight (δ : ℝ) (n : ℕ) :
    LipschitzWith 1 (latitudeWeight δ n) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [latitudeWeight, Real.dist_eq, add_sub_add_left_eq_sub, NNReal.coe_one, one_mul]
  exact (abs_cos_half_sub_le x y).trans (half_le_self (abs_nonneg _))

private theorem latitudeProfile_zero_error {y : ℝ} (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    |S.latitudeProfile 0 y - (Real.cos y + δ)| ≤ δ / Real.pi / 2 := by
  have hX : |S.X 0 (2 * y) - longitude (2 * y)| ≤ δ / Real.pi :=
    (S.errorX 0 (2 * y)).trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [latitudeProfile, latitudeWeight, rate, pow_zero, mul_one, add_comm (Real.cos y) δ,
    add_sub_add_left_eq_sub]
  simpa only [longitude_of_mem (double_latitude_mem hy), mul_div_cancel_left₀ y two_ne_zero] using
    (abs_cos_half_sub_le _ _).trans (div_le_div_of_nonneg_right hX (by norm_num))

theorem coefficient_bounds (n : ℕ) (y : ℝ) :
    0 < S.coefficient n y ∧ |S.coefficient n y| ≤ rate δ n := by
  have hcos := abs_le.mp <| (abs_cos_half_sub_le _ _).trans
    (div_le_div_of_nonneg_right (S.X_step_bound n (2 * y)) (by norm_num : 0 ≤ (2 : ℝ)))
  unfold coefficient latitudeProfile latitudeWeight
  rw [rate_succ] at hcos ⊢
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    linarith only [hcos.1, hcos.2, rate_pos S.delta_pos n]

theorem hasSum_coefficient {y : ℝ} (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    HasSum (fun n => S.coefficient n y) (S.latitudeProfile 0 y - Real.cos y) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n => (S.coefficient_bounds n y).1.le) _).2 ?_
  simpa only [coefficient, Finset.sum_range_sub'] using
    (tendsto_const_nhds (x := S.latitudeProfile 0 y)).sub (S.tendsto_latitudeProfile hy)

def correction (p : ℝ × ℝ) := ∑' n, S.coefficient n p.2 * S.X n p.1

theorem summable_correction (p : ℝ × ℝ) : Summable (fun n => S.coefficient n p.2 * S.X n p.1) :=
  ((summable_rate δ).mul_right Real.pi).of_norm_bounded
    (fun n => norm_mul_le_of_le (S.coefficient_bounds n p.2).2 (S.boundX n p.1))

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
    exact (abs_sub_comm _ _).trans_le ((S.X_step_bound n x).trans (rate_le_rate_add_pi δ _))

def incrementTerm (n : ℕ) (p : ℝ × ℝ) :=
  S.longitudeIncrement n p.1 * S.latitudeProfile n p.2

def scalar (p : ℝ × ℝ) := ∑' n, S.incrementTerm n p

private theorem norm_incrementTerm (n : ℕ) (p : ℝ × ℝ) :
    ‖S.incrementTerm n p‖ ≤ rate (δ + Real.pi) n * (δ + 1) :=
  norm_mul_le_of_le (S.longitudeIncrement_bound n p.1) (S.abs_latitudeWeight_le n (S.X n (2 * p.2)))

theorem continuous_scalar : Continuous S.scalar := by
  have hinc (n : ℕ) : Continuous (S.longitudeIncrement n) := by
    cases n with
    | zero => exact S.continuousX 0
    | succ n => exact (S.continuousX (n + 1)).sub (S.continuousX n)
  have hprofile (n : ℕ) : Continuous (S.latitudeProfile n) :=
    (lipschitzWith_latitudeWeight δ n).continuous.comp
      ((S.continuousX n).comp (continuous_const.mul continuous_id))
  refine continuous_tsum (fun n => ?_) ((summable_rate (δ + Real.pi)).mul_right (δ + 1)) S.norm_incrementTerm
  exact ((hinc n).comp continuous_fst).mul ((hprofile n).comp continuous_snd)

theorem scalar_eq_correction {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) :
    S.scalar p = p.1 * Real.cos p.2 + S.correction p := by
  have hsum : Summable (fun n => S.incrementTerm n p) :=
    ((summable_rate (δ + Real.pi)).mul_right (δ + 1)).of_norm_bounded (fun n => S.norm_incrementTerm n p)
  rw [scalar, hsum.tsum_eq_zero_add, mul_comm p.1 (Real.cos p.2)]
  exact tsum_weighted_increment (S.summable_correction p) ((summable_nat_add_iff 1).2 hsum)
    ((S.tendsto_latitudeProfile hp.2).mul (S.tendsto_X hp.1))

theorem scalar_strictLowerSlope {x x' y : ℝ}
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hx' : x' ∈ Icc (-Real.pi) Real.pi)
    (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hxx' : x < x') :
    Real.cos y * (x' - x) < S.scalar (x', y) - S.scalar (x, y) := by
  obtain ⟨n, hX⟩ := ((S.tendsto_X hx).eventually_lt (S.tendsto_X hx') hxx').exists
  have hsum : S.correction (x, y) < S.correction (x', y) :=
    Summable.tsum_lt_tsum
      (fun k => mul_le_mul_of_nonneg_left (S.monoX k hxx'.le) (S.coefficient_bounds k y).1.le)
      (mul_lt_mul_of_pos_left hX (S.coefficient_bounds n y).1)
      (S.summable_correction (x, y)) (S.summable_correction (x', y))
  rw [S.scalar_eq_correction (p := (x', y)) ⟨hx', hy⟩,
    S.scalar_eq_correction (p := (x, y)) ⟨hx, hy⟩]
  nlinarith only [hsum]

theorem scalar_error {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) :
    |S.scalar p - (Real.cos p.2 + δ) * p.1| ≤ δ := by
  have hcoef := S.hasSum_coefficient hp.2
  have hrate := (hasSum_rate δ).mul_right (1 / 4)
  rw [show δ * 2 * (1 / 4) = δ / 2 by ring] at hrate
  have hcor : |S.scalar p - S.latitudeProfile 0 p.2 * p.1| ≤ δ / 2 := by
    rw [S.scalar_eq_correction hp, show p.1 * Real.cos p.2 + S.correction p - S.latitudeProfile 0 p.2 * p.1 =
      S.correction p - (S.latitudeProfile 0 p.2 - Real.cos p.2) * p.1 by
      ring]
    refine abs_sub_le_of_hasSum_weighted (S.summable_correction p).hasSum (hcoef.mul_right p.1)
      hrate (fun n => (S.coefficient_bounds n p.2).2) (fun n => ?_)
    simpa only [longitude_of_mem hp.1] using
      (S.errorX n p.1).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlat : |S.latitudeProfile 0 p.2 * p.1 - (Real.cos p.2 + δ) * p.1| ≤ δ / 2 := by
    rw [← sub_mul, ← Real.norm_eq_abs]
    exact (norm_mul_le_of_le (S.latitudeProfile_zero_error hp.2) (abs_le.mpr hp.1)).trans_eq
      (by rw [div_mul_eq_mul_div, div_mul_cancel₀ _ Real.pi_ne_zero])
  exact (abs_sub_le ..).trans (by linarith only [hcor, hlat])

def horizontalControl (x : ℝ) := ∑' n, rate (δ + Real.pi) n * S.X n x

theorem horizontal_increment_bound (x x' y : ℝ) :
    |S.correction (x', y) - S.correction (x, y)| ≤ |S.horizontalControl x' - S.horizontalControl x| :=
  abs_tsum_weighted_comp_sub_le (f := fun _ => id) (summable_rate (δ + Real.pi))
    (fun n => (S.coefficient_bounds n y).2.trans (rate_le_rate_add_pi δ n))
    S.monoX S.boundX (fun _ => LipschitzWith.id) S.boundX x x'

theorem vertical_increment_bound (x y y' : ℝ) :
    |S.scalar (x, y') - S.scalar (x, y)| ≤ |S.horizontalControl (2 * y') - S.horizontalControl (2 * y)| :=
  abs_tsum_weighted_comp_sub_le (f := latitudeWeight δ)
    (summable_rate (δ + Real.pi)) (fun n => S.longitudeIncrement_bound n x)
    S.monoX S.boundX (lipschitzWith_latitudeWeight δ)
    (fun n t => S.abs_latitudeWeight_le n (S.X n t)) (2 * y) (2 * y')

theorem horizontal_singular : ∀ᵐ x ∂volume, HasDerivAt S.horizontalControl 0 x :=
  singular_bounded_weighted_tsum S.X (rate (δ + Real.pi))
    (fun n => (rate_pos (add_pos S.delta_pos Real.pi_pos) n).le)
    (summable_rate (δ + Real.pi)) S.boundX S.continuousX S.monoX S.singularX

theorem linearization_bound {p q : ℝ × ℝ} (hp : p ∈ sphereClosedBox) (hq : q ∈ sphereClosedBox) :
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
    _ ≤ _ := (abs_add_le _ _).trans
      (add_le_add (S.horizontal_increment_bound p.1 q.1 p.2)
        (S.vertical_increment_bound q.1 p.2 q.2))

end Staircases

/-- A close approximation to the sinusoidal longitude coordinate with the
prescribed horizontal differential almost everywhere and increasing rows. -/
theorem exists_strict_scalar_flattening {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℝ × ℝ → ℝ, ∃ E : Set (ℝ × ℝ),
      ContinuousOn u sphereClosedBox ∧ MeasurableSet E ∧ E ⊆ sphereLongitudeDomain ∧
      volume (sphereLongitudeDomain \ E) = 0 ∧
      (∀ q ∈ sphereClosedBox, |u q - (Real.cos q.2 + δ) * q.1| ≤ δ) ∧
      (∀ p ∈ sphereClosedBox, ∀ q ∈ sphereClosedBox, p.2 = q.2 → p.1 < q.1 →
        Real.cos p.2 * (q.1 - p.1) < u q - u p) ∧
      ∀ p ∈ E, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  obtain ⟨S⟩ := exists_staircases hδ
  obtain ⟨E, hm, hsub, hnull, hderiv⟩ :=
    exists_scaled_product_derivative_good S.horizontalControl (c := 2) (by norm_num) sphereLongitudeDomain
      isOpen_sphereLongitudeDomain.measurableSet S.horizontal_singular
  refine ⟨S.scalar, E, S.continuous_scalar.continuousOn, hm, hsub, hnull, fun _ => S.scalar_error, ?_, ?_⟩
  · intro p hp q hq hlat hlong
    change _ < S.scalar (q.1, q.2) - S.scalar p
    rw [← hlat]
    exact S.scalar_strictLowerSlope hp.1 hq.1 hp.2 hlong
  · intro p hp
    have hd := hderiv p hp
    apply hasFDerivAt_of_increment_bounds (L := ContinuousLinearMap.fst ℝ ℝ ℝ)
      (M := (2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) hd.1 hd.2
    filter_upwards [isOpen_sphereLongitudeDomain.mem_nhds (hsub hp)] with q hq
    exact S.linearization_bound (sphereLongitudeDomain_subset_box (hsub hp))
      (sphereLongitudeDomain_subset_box hq)

end
end GlobeFlattening
