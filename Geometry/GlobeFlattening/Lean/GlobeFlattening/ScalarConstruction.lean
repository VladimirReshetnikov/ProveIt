import GlobeFlattening.CoordinateRectangles
import GlobeFlattening.SingularSeries
import GlobeFlattening.SingularStaircase
import GlobeFlattening.StaircaseEstimates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The scalar longitude coordinate from singular staircases

Approximate longitude by monotone singular staircases `X n` and rescale
them for latitude as `Y n`. The correction weights are successive drops
of `rate n + cos (Y n y)`. Their positivity gives the strict lower
longitude slope.

The scalar coordinate is the clamped sinusoidal coordinate plus the
longitude correction. Summation by parts shows that finite sums of
longitude increments weighted by `rate n + cos (Y n y)` converge to the same
coordinate. The two formulas bound horizontal and vertical errors by a
single monotone singular sum and its latitude rescaling.
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
  errorX : ∀ n x, |X n x - longitude x| ≤ rate δ n / 4

theorem exists_staircases {δ : ℝ} (hδ : 0 < δ) : Nonempty (Staircases δ) := by
  have hX (n : ℕ) := exists_singular_approx (neg_lt_self Real.pi_pos)
    (div_pos (rate_pos hδ n) (by norm_num : (0 : ℝ) < 4))
  choose X hc hm hr he hd using hX
  exact ⟨⟨hδ, X, hm, hc, hd, fun n x => abs_le.mpr (hr n x), he⟩⟩

namespace Staircases

variable {δ : ℝ} (S : Staircases δ)

private theorem X_step_bound (n : ℕ) (x : ℝ) : |S.X (n + 1) x - S.X n x| ≤ rate δ (n + 1) := by
  have h := abs_sub_le (S.X (n + 1) x) (longitude x) (S.X n x)
  rw [abs_sub_comm (longitude x)] at h
  have hnext := S.errorX (n + 1) x
  rw [rate_succ] at hnext ⊢
  linarith only [h, hnext, S.errorX n x, (rate_pos S.delta_pos n).le]

theorem tendsto_X (x : ℝ) : Tendsto (fun n => S.X n x) atTop (𝓝 (longitude x)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (g := fun n => rate δ n / 4) (fun _ => norm_nonneg _) (fun n => ?_) ?_
  · simpa only [Real.norm_eq_abs] using S.errorX n x
  · simpa only [zero_div] using (summable_rate δ).tendsto_atTop_zero.div_const 4

private def latitudeWeight (δ : ℝ) (n : ℕ) (t : ℝ) := rate δ n + Real.cos (t / 2)

def latitudeProfile (n : ℕ) (y : ℝ) : ℝ := latitudeWeight δ n (S.X n (2 * y))
def coefficient (n : ℕ) (y : ℝ) : ℝ := S.latitudeProfile n y - S.latitudeProfile (n + 1) y

theorem tendsto_latitudeProfile (y : ℝ) :
    Tendsto (fun n => S.latitudeProfile n y) atTop (𝓝 (Real.cos (longitude (2 * y) / 2))) := by
  simpa only [latitudeProfile, latitudeWeight, Function.comp_def, zero_add] using
    (summable_rate δ).tendsto_atTop_zero.add
      ((Real.continuous_cos.tendsto _).comp ((S.tendsto_X (2 * y)).div_const 2))

private theorem abs_cos_half_sub_le (x y : ℝ) :
    |Real.cos (x / 2) - Real.cos (y / 2)| ≤ |x - y| / 2 := by
  simpa [← sub_div, abs_div] using Real.abs_cos_sub_cos_le (x / 2) (y / 2)

theorem coefficient_bounds (n : ℕ) (y : ℝ) :
    0 < S.coefficient n y ∧ |S.coefficient n y| ≤ rate δ n := by
  have hcos := abs_le.mp <| (abs_cos_half_sub_le _ _).trans
    (div_le_div_of_nonneg_right (S.X_step_bound n (2 * y)) (by norm_num : 0 ≤ (2 : ℝ)))
  unfold coefficient latitudeProfile latitudeWeight
  rw [rate_succ] at hcos ⊢
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    linarith only [hcos.1, hcos.2, rate_pos S.delta_pos n]

def correction (p : ℝ × ℝ) := ∑' n, S.coefficient n p.2 * S.X n p.1

private theorem norm_correction_term (n : ℕ) (p : ℝ × ℝ) :
    ‖S.coefficient n p.2 * S.X n p.1‖ ≤ rate δ n * Real.pi :=
  norm_mul_le_of_le (S.coefficient_bounds n p.2).2 (S.boundX n p.1)

private theorem correction_series :
    Continuous S.correction ∧ (∀ p, HasSum (fun n => S.coefficient n p.2 * S.X n p.1) (S.correction p)) := by
  have hu := tendstoUniformly_tsum ((summable_rate δ).mul_right Real.pi) S.norm_correction_term
  refine ⟨hu.continuous (Frequently.of_forall fun N => continuous_finsetSum N fun n _ => ?_), hu.tendsto_at⟩
  have hprofile (k : ℕ) : Continuous (S.latitudeProfile k) := by
    have hX := S.continuousX k
    fun_prop [latitudeProfile, latitudeWeight]
  exact (((hprofile n).sub (hprofile (n + 1))).comp continuous_snd).mul ((S.continuousX n).comp continuous_fst)

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

def scalar (p : ℝ × ℝ) :=
  longitude p.1 * Real.cos (longitude (2 * p.2) / 2) + S.correction p

private theorem continuous_scalar : Continuous S.scalar := by
  have hlong : Continuous longitude := continuous_subtype_val.comp continuous_projIcc
  exact ((hlong.comp continuous_fst).mul
    (Real.continuous_cos.comp ((hlong.comp (continuous_const.mul continuous_snd)).div_const 2))).add
      S.correction_series.1

private theorem tendsto_increment_sum (p : ℝ × ℝ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, S.longitudeIncrement n p.1 * S.latitudeProfile n p.2)
      atTop (𝓝 (S.scalar p)) := by
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  simpa only [Finset.sum_range_succ', longitudeIncrement, scalar] using
    tendsto_sum_weighted_increment (S.correction_series.2 p)
      ((S.tendsto_X p.1).mul (S.tendsto_latitudeProfile p.2))

theorem scalar_eq_correction {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) :
    S.scalar p = p.1 * Real.cos p.2 + S.correction p := by
  simp only [scalar, longitude_of_mem hp.1, longitude_of_mem (double_latitude_mem hp.2),
    mul_div_cancel_left₀ p.2 two_ne_zero]

theorem scalar_strictLowerSlope : StrictLowerSlopeOn S.scalar Real.cos sphereClosedBox := by
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq rfl hxx'
  obtain ⟨n, hX⟩ := ((S.tendsto_X x).eventually_lt (S.tendsto_X x')
    (by rwa [longitude_of_mem hp.1, longitude_of_mem hq.1])).exists
  have hsum : S.correction (x, y) < S.correction (x', y) :=
    Summable.tsum_lt_tsum
      (fun k => mul_le_mul_of_nonneg_left (S.monoX k hxx'.le) (S.coefficient_bounds k y).1.le)
      (mul_lt_mul_of_pos_left hX (S.coefficient_bounds n y).1)
      (S.correction_series.2 (x, y)).summable (S.correction_series.2 (x', y)).summable
  rw [S.scalar_eq_correction hp, S.scalar_eq_correction hq]
  nlinarith only [hsum]

theorem scalar_error {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) :
    dist (flattenCoordinates S.scalar p) (sinusoidalCoordinates p) ≤ δ * 2 * Real.pi := by
  rw [dist_flattenCoordinates_sinusoidalCoordinates, S.scalar_eq_correction hp,
    add_sub_cancel_left, ← Real.norm_eq_abs]
  exact (S.correction_series.2 p).norm_le_of_bounded ((hasSum_rate δ).mul_right Real.pi) (fun n => S.norm_correction_term n p)

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
      · exact abs_sub_le_of_tendsto_weighted_comp (X := S.X) (f := fun _ => id) hcontrol
          (fun n => (S.coefficient_bounds n p.2).2.trans (rate_le_rate_add_pi δ n)) S.monoX
          (fun _ _ _ => le_rfl) p.1 q.1 (S.correction_series.2 p).tendsto_sum_nat (S.correction_series.2 mid).tendsto_sum_nat
      · refine abs_sub_le_of_tendsto_weighted_comp (X := S.X) (f := latitudeWeight δ) hcontrol
          (fun n => S.longitudeIncrement_bound n q.1) S.monoX
          (fun n x y => ?_) (2 * p.2) (2 * q.2) (S.tendsto_increment_sum mid) (S.tendsto_increment_sum q)
        simpa only [latitudeWeight, add_sub_add_left_eq_sub] using
          (abs_cos_half_sub_le y x).trans (half_le_self (abs_nonneg _))

end Staircases

/-- A close approximation to the sinusoidal longitude coordinate with the
prescribed horizontal differential almost everywhere and increasing rows. -/
theorem exists_strict_scalar_flattening {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ × ℝ → ℝ, ∃ E : Set (ℝ × ℝ),
      ContinuousOn u sphereClosedBox ∧ MeasurableSet E ∧ E ⊆ sphereLongitudeDomain ∧
      volume (sphereLongitudeDomain \ E) = 0 ∧
      (∀ q ∈ sphereClosedBox, dist (flattenCoordinates u q) (sinusoidalCoordinates q) ≤ ε) ∧
      StrictLowerSlopeOn u Real.cos sphereClosedBox ∧
      ∀ p ∈ E, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  let δ := ε / (2 * Real.pi)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hscale : δ * 2 * Real.pi = ε := by
    rw [mul_assoc]
    exact div_mul_cancel₀ ε (by positivity)
  obtain ⟨S⟩ := exists_staircases hδ
  obtain ⟨hcontrol, hsingular⟩ := summable_and_singular_weighted_tsum S.X (rate (δ + Real.pi))
    (fun n => (rate_pos (add_pos hδ Real.pi_pos) n).le)
    (summable_rate (δ + Real.pi)) S.boundX S.continuousX S.monoX S.singularX
  obtain ⟨E, hm, hsub, hnull, hderiv⟩ :=
    exists_hasFDerivAt_of_increment_bounds S.horizontalControl (fun p => Real.cos p.2)
      (c := 2) (by norm_num) isOpen_sphereLongitudeDomain hsingular (fun p hp q hq =>
        S.linearization_bound hcontrol (sphereLongitudeDomain_subset_box hp) (sphereLongitudeDomain_subset_box hq))
  exact ⟨S.scalar, E, S.continuous_scalar.continuousOn, hm, hsub, hnull,
    fun _ hq => (S.scalar_error hq).trans_eq hscale, S.scalar_strictLowerSlope, hderiv⟩

end
end GlobeFlattening
