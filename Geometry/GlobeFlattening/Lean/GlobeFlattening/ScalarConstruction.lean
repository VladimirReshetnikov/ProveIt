import GlobeFlattening.CoordinateRectangles
import GlobeFlattening.SingularSeries
import GlobeFlattening.SingularStaircase
import GlobeFlattening.StaircaseEstimates
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The scalar longitude coordinate from singular staircases

Approximate longitude by monotone singular staircases `X n` and rescale
them for latitude as `Y n`. The correction weights are successive drops
of `rate n + cos (Y n y)`. Their positivity gives the strict lower
longitude slope.

Summation by parts expresses the same scalar coordinate with increments of
`X` and coefficients `rate n + cos (Y n y)`. The two expressions bound
horizontal and vertical errors by increments of monotone singular sums.
-/

namespace GlobeFlattening

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

def clamp (a b x : ℝ) : ℝ := max a (min b x)
abbrev longitude := clamp (-Real.pi) Real.pi
def latitude (y : ℝ) := longitude (2 * y) / 2

theorem clamp_eq {a b x : ℝ} (hx : x ∈ Icc a b) : clamp a b x = x := by
  simp [clamp, min_eq_right hx.2, max_eq_right hx.1]

private theorem latitude_eq {y : ℝ} (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) : latitude y = y := by
  have hy' : 2 * y ∈ Icc (-Real.pi) Real.pi := ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
  rw [latitude, longitude, clamp_eq hy']
  ring

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
  have hX (n : ℕ) := exists_singular_approx
    (show -Real.pi < Real.pi by linarith [Real.pi_pos])
    (lt_min (div_pos (rate_pos hδ n) (by norm_num : (0 : ℝ) < 4))
      (by norm_num : (0 : ℝ) < 1 / 4))
  choose X hc hm hr _ _ he hd using hX
  exact ⟨⟨hδ, X, hm, hc, hd, fun n x => abs_le.mpr (hr n x), he⟩⟩

namespace Staircases

variable {δ : ℝ} (S : Staircases δ)

def Y (n : ℕ) (y : ℝ) : ℝ := S.X n (2 * y) / 2

theorem monoY (n : ℕ) : Monotone (S.Y n) := fun _ _ h =>
  div_le_div_of_nonneg_right (S.monoX n (mul_le_mul_of_nonneg_left h (by norm_num))) (by norm_num)

theorem continuousY (n : ℕ) : Continuous (S.Y n) :=
  ((S.continuousX n).comp (continuous_const.mul continuous_id)).div_const 2

theorem singularY (n : ℕ) : ∀ᵐ y ∂volume, HasDerivAt (S.Y n) 0 y := by
  have hscale := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (by norm_num : (2 : ℝ) ≠ 0)
  filter_upwards [hscale.ae (S.singularX n)] with y hy
  change HasDerivAt (fun t => S.X n (2 * t) / 2) 0 y
  simpa [Function.comp_def] using
    (hy.comp y ((hasDerivAt_id y).const_mul (2 : ℝ))).div_const 2

theorem boundY (n : ℕ) (y : ℝ) : |S.Y n y| ≤ Real.pi / 2 := by
  rw [Y, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (S.boundX n (2 * y)) (by norm_num)

theorem errorRateX (n : ℕ) (x : ℝ) : |S.X n x - longitude x| ≤ rate δ n / 4 :=
  (S.errorX n x).trans (min_le_left _ _)

theorem rate_nonneg (S : Staircases δ) (n : ℕ) : 0 ≤ rate δ n := (rate_pos S.delta_pos n).le

theorem abs_rate_le (S : Staircases δ) (n : ℕ) : |rate δ n| ≤ δ := by
  rw [abs_of_nonneg (S.rate_nonneg n)]
  exact mul_le_of_le_one_right S.delta_pos.le (pow_le_one₀ (by norm_num) (by norm_num))

theorem tendsto_X (x : ℝ) : Tendsto (fun n => S.X n x) atTop (𝓝 (longitude x)) :=
  tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (fun _ => norm_nonneg _) (fun n => S.errorRateX n x)
      (by simpa only [zero_div] using (summable_rate δ).tendsto_atTop_zero.div_const 4)

theorem tendsto_Y (y : ℝ) : Tendsto (fun n => S.Y n y) atTop (𝓝 (latitude y)) :=
  (S.tendsto_X (2 * y)).div_const 2

def latitudeProfile (n : ℕ) (y : ℝ) : ℝ := rate δ n + Real.cos (S.Y n y)
def coefficient (n : ℕ) (y : ℝ) : ℝ := S.latitudeProfile n y - S.latitudeProfile (n + 1) y

theorem tendsto_latitudeProfile (y : ℝ) :
    Tendsto (fun n => S.latitudeProfile n y) atTop (𝓝 (Real.cos (latitude y))) := by
  simpa only [latitudeProfile, Function.comp_def, zero_add] using
    (summable_rate δ).tendsto_atTop_zero.add
      ((Real.continuous_cos.tendsto (latitude y)).comp (S.tendsto_Y y))

theorem latitude_cos_error (n : ℕ) (y : ℝ) :
    |Real.cos (S.Y n y) - Real.cos (latitude y)| ≤ rate δ n / 8 := by
  refine (Real.abs_cos_sub_cos_le _ _).trans ?_
  rw [Y, latitude, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right (S.errorRateX n (2 * y)) (by norm_num)).trans_eq (by ring)

theorem coefficient_bounds (n : ℕ) (y : ℝ) :
    0 < S.coefficient n y ∧ S.coefficient n y ≤ rate δ n := by
  have hc := abs_le.mp (S.latitude_cos_error n y)
  have hc' := abs_le.mp (S.latitude_cos_error (n + 1) y)
  unfold coefficient latitudeProfile
  rw [rate_succ] at hc' ⊢
  constructor <;> linarith only [hc.1, hc.2, hc'.1, hc'.2, rate_pos S.delta_pos n]

theorem hasSum_coefficient (y : ℝ) :
    HasSum (fun n => S.coefficient n y) (S.latitudeProfile 0 y - Real.cos (latitude y)) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n => (S.coefficient_bounds n y).1.le) _).2 ?_
  simpa only [coefficient, Finset.sum_range_sub'] using
    (tendsto_const_nhds (x := S.latitudeProfile 0 y)).sub (S.tendsto_latitudeProfile y)

def correctionTerm (n : ℕ) (p : ℝ × ℝ) :=
  S.coefficient n p.2 * S.X n p.1

def correction (p : ℝ × ℝ) := ∑' n, S.correctionTerm n p

def scalar (p : ℝ × ℝ) :=
  longitude p.1 * Real.cos (latitude p.2) + S.correction p

theorem norm_correctionTerm (n : ℕ) (p : ℝ × ℝ) :
    ‖S.correctionTerm n p‖ ≤ Real.pi * rate δ n := by
  obtain ⟨hpos, hle⟩ := S.coefficient_bounds n p.2
  rw [correctionTerm, Real.norm_eq_abs, abs_mul, abs_of_pos hpos, mul_comm Real.pi]
  exact mul_le_mul hle (S.boundX n p.1) (abs_nonneg _) (S.rate_nonneg n)

theorem summable_correction (p : ℝ × ℝ) : Summable (fun n => S.correctionTerm n p) :=
  ((summable_rate δ).mul_left Real.pi).of_norm_bounded (fun n => S.norm_correctionTerm n p)

theorem continuous_scalar : Continuous S.scalar := by
  have hLon : Continuous longitude := by unfold longitude clamp; fun_prop
  have hLat : Continuous latitude := (hLon.comp (continuous_const.mul continuous_id)).div_const 2
  have hprofile (n : ℕ) : Continuous (S.latitudeProfile n) :=
    continuous_const.add (Real.continuous_cos.comp (S.continuousY n))
  have hterm (n : ℕ) : Continuous (S.correctionTerm n) :=
    (((hprofile n).sub (hprofile (n + 1))).comp continuous_snd).mul
      ((S.continuousX n).comp continuous_fst)
  exact ((hLon.comp continuous_fst).mul (Real.continuous_cos.comp (hLat.comp continuous_snd))).add
    (continuous_tsum hterm ((summable_rate δ).mul_left Real.pi) S.norm_correctionTerm)

theorem scalar_strictLowerSlope {x x' y : ℝ}
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hx' : x' ∈ Icc (-Real.pi) Real.pi)
    (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hxx' : x < x') :
    Real.cos y * (x' - x) < S.scalar (x', y) - S.scalar (x, y) := by
  have hlim : Tendsto (fun n => S.X n x) atTop (𝓝 x) := by
    simpa only [longitude, clamp_eq hx] using S.tendsto_X x
  have hlim' : Tendsto (fun n => S.X n x') atTop (𝓝 x') := by
    simpa only [longitude, clamp_eq hx'] using S.tendsto_X x'
  obtain ⟨n, hX⟩ := (hlim.eventually_lt hlim' hxx').exists
  have hsum : S.correction (x, y) < S.correction (x', y) :=
    Summable.tsum_lt_tsum
      (fun k => mul_le_mul_of_nonneg_left (S.monoX k hxx'.le) (S.coefficient_bounds k y).1.le)
      (mul_lt_mul_of_pos_left hX (S.coefficient_bounds n y).1)
      (S.summable_correction (x, y)) (S.summable_correction (x', y))
  simp only [scalar, longitude, clamp_eq hx, clamp_eq hx', latitude_eq hy]
  nlinarith only [hsum]

theorem scalar_error (p : ℝ × ℝ) :
    |S.scalar p - (Real.cos (latitude p.2) + δ) * longitude p.1| ≤ δ := by
  let x := longitude p.1
  have hcoef := S.hasSum_coefficient p.2
  have hrate := (hasSum_rate δ).mul_right (1 / 4)
  rw [show δ * 2 * (1 / 4) = δ / 2 by ring] at hrate
  have hcor : |S.scalar p - S.latitudeProfile 0 p.2 * x| ≤ δ / 2 := by
    rw [show S.scalar p - S.latitudeProfile 0 p.2 * x =
      S.correction p - (S.latitudeProfile 0 p.2 - Real.cos (latitude p.2)) * x by
      simp only [scalar, x]; ring,
      correction, ← hcoef.tsum_eq, ← tsum_mul_right,
      ← (S.summable_correction p).tsum_sub (hcoef.summable.mul_right x)]
    refine tsum_of_norm_bounded (f := fun n => S.correctionTerm n p - S.coefficient n p.2 * x)
      hrate fun n => ?_
    obtain ⟨hpos, hle⟩ := S.coefficient_bounds n p.2
    rw [Real.norm_eq_abs, correctionTerm, ← mul_sub, abs_mul, abs_of_pos hpos]
    exact mul_le_mul hle ((S.errorX n p.1).trans (min_le_right _ _)) (abs_nonneg _) (S.rate_nonneg n)
  have hlat : |S.latitudeProfile 0 p.2 * x - (Real.cos (latitude p.2) + δ) * x| ≤ δ / 2 := by
    rw [← sub_mul, latitudeProfile, rate, pow_zero, mul_one, add_comm (Real.cos (latitude p.2)) δ,
      add_sub_add_left_eq_sub, abs_mul]
    have hcos := S.latitude_cos_error 0 p.2
    simp only [rate, pow_zero, mul_one] at hcos
    have hx : |x| ≤ Real.pi := abs_le.mpr
      ⟨le_max_left _ _, max_le (neg_le_self Real.pi_pos.le) (min_le_left _ _)⟩
    linarith only [mul_le_mul hcos (hx.trans Real.pi_lt_four.le) (abs_nonneg _)
      (div_nonneg S.delta_pos.le (by norm_num))]
  exact (abs_sub_le ..).trans (by linarith only [hcor, hlat])

def horizontalControl (x : ℝ) := ∑' n, rate δ n * S.X n x

theorem horizontal_increment_bound (x x' y : ℝ) :
    |S.correction (x', y) - S.correction (x, y)| ≤ |S.horizontalControl x' - S.horizontalControl x| :=
  abs_tsum_weighted_sub_le (summable_rate δ)
    (fun n => let h := S.coefficient_bounds n y; ⟨h.1.le, h.2⟩) S.monoX S.boundX x x'

def longitudeStream : ℕ → ℝ → ℝ
  | 0 => 0
  | n + 1 => S.X n

def longitudeIncrement (n : ℕ) (x : ℝ) :=
  S.longitudeStream (n + 1) x - S.longitudeStream n x

def incrementWeight (δ : ℝ) : ℕ → ℝ := Function.update (rate δ) 0 Real.pi

theorem summable_incrementWeight (δ : ℝ) : Summable (incrementWeight δ) :=
  (summable_rate δ).update 0 Real.pi

theorem longitudeIncrement_bound (n : ℕ) (x : ℝ) :
    |S.longitudeIncrement n x| ≤ incrementWeight δ n := by
  cases n with
  | zero => simpa [longitudeIncrement, longitudeStream, incrementWeight] using S.boundX 0 x
  | succ n =>
    simp only [longitudeIncrement, longitudeStream, incrementWeight,
      Function.update_of_ne (Nat.succ_ne_zero n)]
    calc
      _ ≤ |S.X (n + 1) x - longitude x| + |longitude x - S.X n x| := abs_sub_le ..
      _ ≤ rate δ (n + 1) / 4 + rate δ n / 4 := by
        rw [abs_sub_comm (longitude x)]
        exact add_le_add (S.errorRateX _ x) (S.errorRateX _ x)
      _ ≤ _ := by rw [rate_succ]; linarith only [S.rate_nonneg n]

theorem scalar_series (x y : ℝ) :
    S.scalar (x, y) = ∑' n, (rate δ n + Real.cos (S.Y n y)) * S.longitudeIncrement n x := by
  have h := tsum_weighted_increment (A := fun n => S.longitudeStream n x)
    (e := fun n => S.latitudeProfile n y) rfl (S.summable_correction (x, y))
    (summable_add_cos_mul (summable_incrementWeight δ)
      (fun n => S.longitudeIncrement_bound n x) S.abs_rate_le)
    ((S.tendsto_latitudeProfile y).mul (S.tendsto_X x))
  change (∑' n, (rate δ n + Real.cos (S.Y n y)) * S.longitudeIncrement n x) =
    Real.cos (latitude y) * longitude x + S.correction (x, y) at h
  simpa only [scalar, mul_comm (longitude x) (Real.cos (latitude y))] using h.symm

def verticalControl (y : ℝ) := ∑' n, incrementWeight δ n * S.Y n y

theorem vertical_increment_bound (x y y' : ℝ) :
    |S.scalar (x, y') - S.scalar (x, y)| ≤ |S.verticalControl y' - S.verticalControl y| := by
  rw [S.scalar_series x y', S.scalar_series x y]
  exact abs_tsum_cos_sub_le_of_bounded (summable_incrementWeight δ)
    (fun n => S.longitudeIncrement_bound n x) S.abs_rate_le S.monoY S.boundY y y'

theorem horizontal_singular : ∀ᵐ x ∂volume, HasDerivAt S.horizontalControl 0 x :=
  singular_bounded_weighted_tsum S.X (rate δ) S.rate_nonneg
    (summable_rate δ) (fun x => ⟨Real.pi, fun n => S.boundX n x⟩)
    S.monoX S.singularX

theorem vertical_singular : ∀ᵐ x ∂volume, HasDerivAt S.verticalControl 0 x :=
  singular_bounded_weighted_tsum S.Y (incrementWeight δ)
    (fun n => (abs_nonneg _).trans (S.longitudeIncrement_bound n 0))
    (summable_incrementWeight δ) (fun y => ⟨Real.pi / 2, fun n => S.boundY n y⟩)
    S.monoY S.singularY

theorem linearization_bound {p q : ℝ × ℝ} (hp : p ∈ sphereClosedBox) (hq : q ∈ sphereClosedBox) :
    |S.scalar q - S.scalar p - Real.cos p.2 * (q.1 - p.1)| ≤
      |S.horizontalControl q.1 - S.horizontalControl p.1| +
        |S.verticalControl q.2 - S.verticalControl p.2| := by
  let mid := (q.1, p.2)
  have h : S.scalar mid - S.scalar p - Real.cos p.2 * (q.1 - p.1) =
      S.correction mid - S.correction p := by
    have hx : p.1 ∈ Icc (-Real.pi) Real.pi := hp.1
    have hx' : q.1 ∈ Icc (-Real.pi) Real.pi := hq.1
    have hy : p.2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := hp.2
    simp only [scalar, longitude, mid, clamp_eq hx, clamp_eq hx', latitude_eq hy]
    ring
  rw [show S.scalar q - S.scalar p - Real.cos p.2 * (q.1 - p.1) =
    (S.correction mid - S.correction p) + (S.scalar q - S.scalar mid) by rw [← h]; ring]
  exact (abs_add_le _ _).trans
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
    exists_product_derivative_good S.horizontalControl S.verticalControl sphereLongitudeDomain
      isOpen_sphereLongitudeDomain.measurableSet S.horizontal_singular S.vertical_singular
  refine ⟨S.scalar, E, S.continuous_scalar.continuousOn, hm, hsub, hnull, ?_, ?_, ?_⟩
  · intro p hp
    simpa only [longitude, clamp_eq hp.1, latitude_eq hp.2] using S.scalar_error p
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq hlat hlong
    change y = y' at hlat
    subst y'
    exact S.scalar_strictLowerSlope hp.1 hq.1 hp.2 hlong
  · intro p hp
    have hd := hderiv p hp
    apply hasFDerivAt_of_increment_bounds hd.1 hd.2
    filter_upwards [isOpen_sphereLongitudeDomain.mem_nhds (hsub hp)] with q hq
    exact S.linearization_bound (sphereLongitudeDomain_subset_box (hsub hp))
      (sphereLongitudeDomain_subset_box hq)

/-- The scalar construction also supplies the nonstrict row slope bound. -/
theorem exists_scalar_flattening {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℝ × ℝ → ℝ, ∃ E : Set (ℝ × ℝ),
      ContinuousOn u sphereClosedBox ∧ MeasurableSet E ∧ E ⊆ sphereLongitudeDomain ∧
      volume (sphereLongitudeDomain \ E) = 0 ∧
      (∀ q ∈ sphereClosedBox, |u q - (Real.cos q.2 + δ) * q.1| ≤ δ) ∧
      (∀ p ∈ sphereClosedBox, ∀ q ∈ sphereClosedBox, p.2 = q.2 → p.1 ≤ q.1 →
        Real.cos p.2 * (q.1 - p.1) ≤ u q - u p) ∧
      ∀ p ∈ E, HasFDerivAt u (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  obtain ⟨u, E, hcu, hE, hsub, hnull, hclose, hslope, hderiv⟩ :=
    exists_strict_scalar_flattening hδ
  refine ⟨u, E, hcu, hE, hsub, hnull, hclose, ?_, hderiv⟩
  intro p hp q hq hlat hlong
  rcases hlong.lt_or_eq with h | h
  · exact (hslope p hp q hq hlat h).le
  · obtain rfl : p = q := Prod.ext h hlat
    simp

end
end GlobeFlattening
