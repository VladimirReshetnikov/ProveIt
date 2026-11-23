import GlobeFlattening.SingularSeries
import GlobeFlattening.SingularStaircase
import GlobeFlattening.SphereChart
import GlobeFlattening.StaircaseEstimates
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The scalar longitude coordinate from singular staircases

Approximate longitude and latitude by monotone singular staircases `X n`
and `Y n`. For decreasing geometric rates, the correction weights are the
successive drops of `rate n + cos (Y n y) - cos y` on the chart. Their
nonnegativity preserves the lower longitude slope.

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
abbrev latitude := clamp (-(Real.pi / 2)) (Real.pi / 2)

theorem clamp_eq {a b x : ℝ} (hx : x ∈ Icc a b) : clamp a b x = x := by
  simp [clamp, min_eq_right hx.2, max_eq_right hx.1]

private theorem continuous_clamp (a b : ℝ) : Continuous (clamp a b) := by
  unfold clamp
  fun_prop

def rate (δ : ℝ) (n : ℕ) := δ * (2⁻¹ : ℝ)^n

private theorem rate_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < rate δ n := by
  unfold rate
  positivity

theorem rate_succ (δ : ℝ) (n : ℕ) : rate δ (n + 1) = rate δ n / 2 := by
  rw [rate, pow_succ, ← mul_assoc, ← rate, div_eq_mul_inv]

theorem summable_rate (δ : ℝ) : Summable (rate δ) :=
  (summable_geometric_of_norm_lt_one (by norm_num : ‖(2⁻¹ : ℝ)‖ < 1)).mul_left δ

structure Staircases (δ : ℝ) where
  delta_pos : 0 < δ
  X : ℕ → ℝ → ℝ
  Y : ℕ → ℝ → ℝ
  monoX : ∀ n, Monotone (X n)
  monoY : ∀ n, Monotone (Y n)
  continuousX : ∀ n, Continuous (X n)
  continuousY : ∀ n, Continuous (Y n)
  singularX : ∀ n, ∀ᵐ x ∂volume, HasDerivAt (X n) 0 x
  singularY : ∀ n, ∀ᵐ y ∂volume, HasDerivAt (Y n) 0 y
  boundX : ∀ n x, |X n x| ≤ Real.pi
  boundY : ∀ n y, |Y n y| ≤ Real.pi / 2
  errorRateX : ∀ n x, |X n x - longitude x| ≤ rate δ n
  errorX : ∀ n x, |X n x - longitude x| ≤ 1 / 4
  errorY : ∀ n y, |Y n y - latitude y| ≤ rate δ n / 8

theorem exists_staircases {δ : ℝ} (hδ : 0 < δ) : Nonempty (Staircases δ) := by
  have hX (n : ℕ) := exists_singular_approx
    (show -Real.pi < Real.pi by linarith [Real.pi_pos])
    (lt_min (rate_pos hδ n) (by norm_num : 0 < (1 / 4 : ℝ)))
  have hY (n : ℕ) := exists_singular_approx
    (show -(Real.pi / 2) < Real.pi / 2 by linarith [Real.pi_pos])
    (div_pos (rate_pos hδ n) (by norm_num : (0 : ℝ) < 8))
  choose X hXc hXm hXr _hXa _hXb hXe hXd using hX
  choose Y hYc hYm hYr _hYa _hYb hYe hYd using hY
  exact ⟨{
    delta_pos := hδ
    X := X
    Y := Y
    monoX := hXm
    monoY := hYm
    continuousX := hXc
    continuousY := hYc
    singularX := hXd
    singularY := hYd
    boundX := fun n x => abs_le.mpr (hXr n x)
    boundY := fun n y => abs_le.mpr (hYr n y)
    errorRateX := fun n x => (hXe n x).trans (min_le_left _ _)
    errorX := fun n x => (hXe n x).trans (min_le_right _ _)
    errorY := hYe }⟩

namespace Staircases

variable {δ : ℝ} (S : Staircases δ)

theorem rate_nonneg (S : Staircases δ) (n : ℕ) : 0 ≤ rate δ n := (rate_pos S.delta_pos n).le

theorem abs_rate_le (S : Staircases δ) (n : ℕ) : |rate δ n| ≤ δ := by
  rw [abs_of_nonneg (S.rate_nonneg n)]
  exact mul_le_of_le_one_right S.delta_pos.le (pow_le_one₀ (by norm_num) (by norm_num))

theorem tendsto_X (x : ℝ) : Tendsto (fun n => S.X n x) atTop (𝓝 (longitude x)) :=
  tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (fun _ => norm_nonneg _) (fun n => S.errorRateX n x)
      (summable_rate δ).tendsto_atTop_zero

def excess (n : ℕ) (y : ℝ) : ℝ := rate δ n + Real.cos (S.Y n y) - Real.cos (latitude y)
def coefficient (n : ℕ) (y : ℝ) : ℝ := S.excess n y - S.excess (n + 1) y

theorem excess_error (n : ℕ) (y : ℝ) : |S.excess n y - rate δ n| ≤ rate δ n / 8 := by
  rw [show S.excess n y - rate δ n = Real.cos (S.Y n y) - Real.cos (latitude y) by
    unfold excess
    ring]
  exact (Real.abs_cos_sub_cos_le _ _).trans (S.errorY n y)

theorem excess_bounds (n : ℕ) (y : ℝ) :
    7 * rate δ n / 8 ≤ S.excess n y ∧ S.excess n y ≤ 9 * rate δ n / 8 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (S.excess_error n y)
  constructor <;> linarith only [hlo, hhi]

theorem coefficient_bounds (n : ℕ) (y : ℝ) :
    rate δ n / 4 ≤ S.coefficient n y ∧ S.coefficient n y ≤ rate δ n := by
  have hc := S.excess_bounds n y
  have hc' := S.excess_bounds (n + 1) y
  rw [rate_succ] at hc'
  unfold coefficient
  constructor <;> linarith only [hc.1, hc.2, hc'.1, hc'.2, S.rate_nonneg n]

theorem coefficient_pos (n : ℕ) (y : ℝ) : 0 < S.coefficient n y :=
  (div_pos (rate_pos S.delta_pos n) (by norm_num)).trans_le (S.coefficient_bounds n y).1

theorem abs_excess_le (n : ℕ) (y : ℝ) : |S.excess n y| ≤ 2 * rate δ n := by
  have h := S.excess_bounds n y
  rw [abs_of_nonneg (by linarith only [h.1, S.rate_nonneg n])]
  linarith only [h.2, S.rate_nonneg n]

theorem summable_excess (y : ℝ) : Summable (fun n => S.excess n y) :=
  ((summable_rate δ).mul_left 2).of_norm_bounded (fun n => S.abs_excess_le n y)

theorem antitone_excess (y : ℝ) : Antitone (fun n => S.excess n y) :=
  antitone_nat_of_succ_le (fun n => sub_nonneg.mp (S.coefficient_pos n y).le)

theorem hasSum_coefficient (y : ℝ) : HasSum (fun n => S.coefficient n y) (S.excess 0 y) :=
  hasSum_antitone_drop (S.antitone_excess y) (S.summable_excess y).tendsto_atTop_zero

def correctionTerm (n : ℕ) (p : ℝ × ℝ) :=
  S.coefficient n p.2 * S.X n p.1

def correction (p : ℝ × ℝ) := ∑' n, S.correctionTerm n p

def scalar (p : ℝ × ℝ) :=
  longitude p.1 * Real.cos (latitude p.2) + S.correction p

theorem norm_correctionTerm (n : ℕ) (p : ℝ × ℝ) :
    ‖S.correctionTerm n p‖ ≤ Real.pi * rate δ n := by
  rw [correctionTerm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (S.coefficient_pos n p.2).le,
    mul_comm Real.pi]
  exact mul_le_mul (S.coefficient_bounds n p.2).2 (S.boundX n p.1) (abs_nonneg _)
    (S.rate_nonneg n)

theorem summable_correction (p : ℝ × ℝ) : Summable (fun n => S.correctionTerm n p) :=
  ((summable_rate δ).mul_left Real.pi).of_norm_bounded (fun n => S.norm_correctionTerm n p)

theorem continuous_scalar : Continuous S.scalar := by
  have hLat : Continuous latitude := continuous_clamp _ _
  have hLon : Continuous longitude := continuous_clamp _ _
  have he (n : ℕ) : Continuous (S.excess n) :=
    (continuous_const.add (Real.continuous_cos.comp (S.continuousY n))).sub
      (Real.continuous_cos.comp hLat)
  have hterm (n : ℕ) : Continuous (S.correctionTerm n) :=
    (((he n).sub (he (n+1))).comp continuous_snd).mul ((S.continuousX n).comp continuous_fst)
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
      (fun k => mul_le_mul_of_nonneg_left (S.monoX k hxx'.le) (S.coefficient_pos k y).le)
      (mul_lt_mul_of_pos_left hX (S.coefficient_pos n y))
      (S.summable_correction (x, y)) (S.summable_correction (x', y))
  simp only [scalar, longitude, latitude, clamp_eq hx, clamp_eq hx', clamp_eq hy]
  nlinarith only [hsum]

theorem scalar_error {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) :
    |S.scalar p - (Real.cos p.2 + δ) * p.1| ≤ δ := by
  have hx : p.1 ∈ Icc (-Real.pi) Real.pi := hp.1
  have hy : p.2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := hp.2
  have hcoef := S.hasSum_coefficient p.2
  have hcor : |S.correction p - S.excess 0 p.2 * p.1| ≤ (1 / 4) * S.excess 0 p.2 := by
    have h := abs_tsum_sub_le_of_termwise (S.summable_correction p) (hcoef.summable.mul_right p.1)
      (hcoef.summable.mul_left (1 / 4)) summable_zero fun n => ?_
    · simpa only [correction, tsum_mul_right, tsum_mul_left, hcoef.tsum_eq, tsum_zero, sub_zero] using h
    · have hn := (S.coefficient_pos n p.2).le
      rw [correctionTerm, sub_zero, ← mul_sub, abs_mul, abs_of_nonneg hn, mul_comm (1 / 4)]
      exact mul_le_mul_of_nonneg_left (by simpa only [longitude, clamp_eq hx] using S.errorX n p.1) hn
  have hlat : |(S.excess 0 p.2 - δ) * p.1| ≤ δ / 2 := by
    have h := S.excess_error 0 p.2
    simp only [rate, pow_zero, mul_one] at h
    rw [abs_mul]
    have hx' := (abs_le.mpr hx).trans Real.pi_lt_four.le
    linarith only [mul_le_mul h hx' (abs_nonneg _) (div_nonneg S.delta_pos.le (by norm_num))]
  rw [show S.scalar p - (Real.cos p.2 + δ) * p.1 =
      (S.correction p - S.excess 0 p.2 * p.1) + (S.excess 0 p.2 - δ) * p.1 by
    rw [scalar, longitude, latitude, clamp_eq hx, clamp_eq hy]
    ring]
  have h0 := (S.excess_bounds 0 p.2).2
  simp only [rate, pow_zero, mul_one] at h0
  exact (abs_add_le _ _).trans (by linarith only [hcor, hlat, h0, S.delta_pos])

def horizontalControl (x : ℝ) := ∑' n, rate δ n * S.X n x

theorem horizontal_increment_bound (x x' y : ℝ) :
    |S.correction (x', y) - S.correction (x, y)| ≤ |S.horizontalControl x' - S.horizontalControl x| :=
  abs_tsum_weighted_sub_le (summable_rate δ)
    (fun n => ⟨(S.coefficient_pos n y).le, (S.coefficient_bounds n y).2⟩) S.monoX S.boundX x x'

def longitudeStream : ℕ → ℝ → ℝ
  | 0 => 0
  | n + 1 => S.X n

def longitudeIncrement (n : ℕ) (x : ℝ) :=
  S.longitudeStream (n + 1) x - S.longitudeStream n x

def incrementWeight (δ : ℝ) : ℕ → ℝ
  | 0 => Real.pi
  | n + 1 => 2 * rate δ n

theorem summable_incrementWeight (δ : ℝ) : Summable (incrementWeight δ) := by
  apply (summable_nat_add_iff 1).mp
  exact (summable_rate δ).mul_left 2

theorem longitudeIncrement_bound (n : ℕ) (x : ℝ) :
    |S.longitudeIncrement n x| ≤ incrementWeight δ n := by
  cases n with
  | zero => simpa [longitudeIncrement, longitudeStream, incrementWeight] using S.boundX 0 x
  | succ n =>
    change |S.X (n + 1) x - S.X n x| ≤ 2 * rate δ n
    calc
      _ ≤ |S.X (n + 1) x - longitude x| + |longitude x - S.X n x| := abs_sub_le ..
      _ ≤ rate δ (n + 1) + rate δ n := by
        rw [abs_sub_comm (longitude x)]
        exact add_le_add (S.errorRateX _ x) (S.errorRateX _ x)
      _ ≤ _ := by rw [rate_succ]; linarith only [S.rate_nonneg n]

theorem summable_longitudeIncrement (x : ℝ) : Summable (fun n => S.longitudeIncrement n x) :=
  (summable_incrementWeight δ).of_norm_bounded (fun n => S.longitudeIncrement_bound n x)

theorem tsum_longitudeIncrement (x : ℝ) : (∑' n, S.longitudeIncrement n x) = longitude x :=
  tsum_increment (A := fun n => S.longitudeStream n x) rfl
    (S.summable_longitudeIncrement x) (S.tendsto_X x)

theorem scalar_series (x y : ℝ) :
    S.scalar (x, y) = ∑' n, (rate δ n + Real.cos (S.Y n y)) * S.longitudeIncrement n x := by
  have heq : S.correction (x, y) = ∑' n, S.excess n y * S.longitudeIncrement n x :=
    tsum_weighted_increment_of_antitone (A := fun n => S.longitudeStream n x)
      rfl (S.antitone_excess y) (S.summable_excess y).tendsto_atTop_zero
      (S.summable_longitudeIncrement x) (S.boundX · x)
  have hEbound (n : ℕ) : |S.excess n y| ≤ 2 * δ :=
    (S.abs_excess_le n y).trans (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (S.abs_rate_le n)) (by norm_num))
  have hEΔ := summable_mul_of_abs_le (summable_incrementWeight δ) hEbound
    (fun n => S.longitudeIncrement_bound n x)
  have hbase := (S.summable_longitudeIncrement x).mul_left (Real.cos (latitude y))
  change longitude x * Real.cos (latitude y) + S.correction (x, y) = _
  rw [heq, ← S.tsum_longitudeIncrement x, mul_comm _ (Real.cos (latitude y)),
    ← tsum_mul_left, ← hbase.tsum_add hEΔ]
  congr 1
  funext n
  unfold excess
  ring

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
    simp only [scalar, longitude, latitude, mid, clamp_eq hx, clamp_eq hx', clamp_eq hy]
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
  have hbox : sphereLongitudeDomain ⊆ sphereClosedBox :=
    prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  refine ⟨S.scalar, E, S.continuous_scalar.continuousOn, hm, hsub, hnull,
    fun _ hp => S.scalar_error hp, ?_, ?_⟩
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq hlat hlong
    change y = y' at hlat
    subst y'
    exact S.scalar_strictLowerSlope hp.1 hq.1 hp.2 hlong
  · intro p hp
    have hd := hderiv p hp
    apply hasFDerivAt_of_increment_bounds hd.1 hd.2
    filter_upwards [isOpen_sphereLongitudeDomain.mem_nhds (hsub hp)] with q hq
    exact S.linearization_bound (hbox (hsub hp)) (hbox hq)

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
