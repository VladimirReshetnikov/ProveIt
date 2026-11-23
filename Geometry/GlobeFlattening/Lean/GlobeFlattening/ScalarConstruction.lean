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

def rate (δ : ℝ) (n : ℕ) := δ * (2⁻¹ : ℝ)^n

theorem rate_succ (δ : ℝ) (n : ℕ) : rate δ (n + 1) = rate δ n / 2 := by
  rw [rate, pow_succ, ← mul_assoc, ← rate, div_eq_mul_inv]

theorem summable_rate (δ : ℝ) : Summable (rate δ) :=
  (summable_geometric_of_norm_lt_one (by norm_num : ‖(2⁻¹ : ℝ)‖ < 1)).mul_left δ

structure Staircases (δ : ℝ) where
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
  errorY : ∀ n y, |Y n y - latitude y| ≤ rate δ n / (4 * Real.pi)

theorem exists_staircases {δ : ℝ} (hδ : 0 < δ) : Nonempty (Staircases δ) := by
  have hrate (n : ℕ) : 0 < rate δ n := by
    unfold rate
    positivity
  have hX (n : ℕ) := exists_singular_approx
    (show -Real.pi < Real.pi by linarith [Real.pi_pos])
    (lt_min (hrate n) (by norm_num : 0 < (1 / 4 : ℝ)))
  have hY (n : ℕ) := exists_singular_approx
    (show -(Real.pi / 2) < Real.pi / 2 by linarith [Real.pi_pos])
    (div_pos (hrate n) (by positivity : 0 < 4 * Real.pi))
  choose X hXc hXm hXr _hXa _hXb hXe hXd using hX
  choose Y hYc hYm hYr _hYa _hYb hYe hYd using hY
  exact ⟨{
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

def excess (n : ℕ) (y : ℝ) : ℝ := rate δ n + Real.cos (S.Y n y) - Real.cos (latitude y)
def coefficient (n : ℕ) (y : ℝ) : ℝ := S.excess n y - S.excess (n + 1) y

theorem cos_error (n : ℕ) (y : ℝ) :
    |Real.cos (S.Y n y) - Real.cos (latitude y)| ≤ rate δ n / (4 * Real.pi) :=
  (Real.abs_cos_sub_cos_le _ _).trans (S.errorY n y)

theorem excess_bounds (n : ℕ) (y : ℝ) :
    3 * rate δ n / 4 ≤ S.excess n y ∧ S.excess n y ≤ 5 * rate δ n / 4 := by
  have hcos := S.cos_error n y
  have hrate : 0 ≤ rate δ n := (abs_nonneg _).trans (S.errorRateX n 0)
  have hden : 0 < 4 * Real.pi := by positivity
  have hquotient : rate δ n / (4 * Real.pi) ≤ rate δ n / 4 :=
    div_le_div_of_nonneg_left hrate (by norm_num) (by linarith [Real.pi_gt_three])
  have h := abs_le.mp (hcos.trans hquotient)
  unfold excess
  constructor <;> linarith

theorem coefficient_bounds (n : ℕ) (y : ℝ) :
    0 ≤ S.coefficient n y ∧ S.coefficient n y ≤ 2 * rate δ n := by
  have hc := S.excess_bounds n y
  have hc' := S.excess_bounds (n + 1) y
  rw [rate_succ] at hc'
  have hrate : 0 ≤ rate δ n := (abs_nonneg _).trans (S.errorRateX n 0)
  unfold coefficient
  constructor <;> linarith [hc.1, hc.2, hc'.1, hc'.2]

theorem summable_excess (y : ℝ) : Summable (fun n => S.excess n y) := by
  apply ((summable_rate δ).mul_left 2).of_norm_bounded
  intro n
  have hrate : 0 ≤ rate δ n := (abs_nonneg _).trans (S.errorRateX n 0)
  have h := S.excess_bounds n y
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1])]
  linarith [h.2]

theorem summable_coefficient (y : ℝ) : Summable (fun n => S.coefficient n y) := by
  apply ((summable_rate δ).mul_left 2).of_norm_bounded
  intro n
  have h := S.coefficient_bounds n y
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem tsum_coefficient (y : ℝ) : (∑' n, S.coefficient n y) = S.excess 0 y := by
  have hs := (S.summable_coefficient y).hasSum.tendsto_sum_nat
  simp only [coefficient, Finset.sum_range_sub'] at hs
  apply tendsto_nhds_unique hs
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := S.excess 0 y)).sub (S.summable_excess y).tendsto_atTop_zero

def correctionTerm (n : ℕ) (p : ℝ × ℝ) :=
  S.coefficient n p.2 * S.X n p.1

def scalar (p : ℝ × ℝ) :=
  longitude p.1 * Real.cos (latitude p.2) + ∑' n, S.correctionTerm n p

theorem norm_correctionTerm (n : ℕ) (p : ℝ × ℝ) :
    ‖S.correctionTerm n p‖ ≤ (2 * Real.pi) * rate δ n := by
  have h := S.coefficient_bounds n p.2
  rw [correctionTerm, Real.norm_eq_abs, abs_mul, abs_of_nonneg h.1]
  calc
    _ ≤ (2 * rate δ n) * Real.pi :=
      mul_le_mul h.2 (S.boundX _ _) (abs_nonneg _) (h.1.trans h.2)
    _ = _ := by ring

theorem summable_correction (p : ℝ × ℝ) : Summable (fun n => S.correctionTerm n p) :=
  ((summable_rate δ).mul_left (2 * Real.pi)).of_norm_bounded (fun n => S.norm_correctionTerm n p)

theorem continuous_scalar : Continuous S.scalar := by
  have hLat : Continuous latitude := by unfold latitude clamp; fun_prop
  have he (n : ℕ) : Continuous (S.excess n) :=
    (continuous_const.add (Real.continuous_cos.comp (S.continuousY n))).sub
      (Real.continuous_cos.comp hLat)
  have ht (n : ℕ) : Continuous (S.correctionTerm n) :=
    (((he n).sub (he (n+1))).comp continuous_snd).mul ((S.continuousX n).comp continuous_fst)
  have hsum : Continuous (fun p => ∑' n, S.correctionTerm n p) :=
    (tendstoUniformly_tsum_nat ((summable_rate δ).mul_left (2 * Real.pi))
      S.norm_correctionTerm).continuous
      (Eventually.of_forall (fun N => continuous_finsetSum (Finset.range N) fun n _ => ht n)).frequently
  have hLon : Continuous longitude := by unfold longitude clamp; fun_prop
  exact ((hLon.comp continuous_fst).mul (Real.continuous_cos.comp (hLat.comp continuous_snd))).add hsum

theorem coefficient_pos (hδ : 0 < δ) (n : ℕ) (y : ℝ) : 0 < S.coefficient n y := by
  have hnow := (S.excess_bounds n y).1
  have hnext := (S.excess_bounds (n + 1) y).2
  rw [rate_succ] at hnext
  have hrate : 0 < rate δ n := by unfold rate; positivity
  unfold coefficient
  linarith only [hnow, hnext, hrate]

theorem scalar_strictLowerSlope (hδ : 0 < δ) {x x' y : ℝ}
    (hx : x ∈ Icc (-Real.pi) Real.pi) (hx' : x' ∈ Icc (-Real.pi) Real.pi)
    (hy : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hxx' : x < x') :
    Real.cos y * (x' - x) < S.scalar (x', y) - S.scalar (x, y) := by
  obtain ⟨n, hn⟩ := ((tendsto_order.1 (summable_rate δ).tendsto_atTop_zero).2
    ((x' - x) / 2) (half_pos (sub_pos.mpr hxx'))).exists
  have hxerr := (abs_le.mp (S.errorRateX n x)).2
  have hxerr' := (abs_le.mp (S.errorRateX n x')).1
  rw [longitude, clamp_eq hx] at hxerr
  rw [longitude, clamp_eq hx'] at hxerr'
  have hX : S.X n x < S.X n x' := by linarith only [hn, hxerr, hxerr']
  have hsum : (∑' n, S.correctionTerm n (x, y)) < ∑' n, S.correctionTerm n (x', y) :=
    Summable.tsum_lt_tsum
      (fun k => mul_le_mul_of_nonneg_left (S.monoX k hxx'.le) (S.coefficient_bounds k y).1)
      (mul_lt_mul_of_pos_left hX (S.coefficient_pos hδ n y))
      (S.summable_correction (x, y)) (S.summable_correction (x', y))
  simp only [scalar, longitude, latitude, clamp_eq hx, clamp_eq hx', clamp_eq hy]
  nlinarith only [hsum]

theorem scalar_error {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) :
    |S.scalar p - (Real.cos p.2 + δ) * p.1| ≤ δ := by
  have hx : p.1 ∈ Icc (-Real.pi) Real.pi := hp.1
  have hy : p.2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := hp.2
  have hn : ∀ n, 0 ≤ S.coefficient n p.2 := fun n => (S.coefficient_bounds n p.2).1
  have hsub (n : ℕ) : ‖S.coefficient n p.2 * (S.X n p.1 - p.1)‖ ≤
      (1 / 4) * S.coefficient n p.2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hn n), mul_comm (1/4 : ℝ)]
    exact mul_le_mul_of_nonneg_left (by simpa only [longitude, clamp_eq hx] using S.errorX n p.1) (hn n)
  have hcor := tsum_of_norm_bounded (((S.summable_coefficient p.2).mul_left (1/4 : ℝ)).hasSum) hsub
  rw [Real.norm_eq_abs, tsum_mul_left, S.tsum_coefficient] at hcor
  have hrewrite : (∑' n, S.coefficient n p.2 * (S.X n p.1 - p.1)) =
      (∑' n, S.correctionTerm n p) - S.excess 0 p.2 * p.1 := by
    simp_rw [mul_sub]
    change (∑' n, (S.correctionTerm n p - S.coefficient n p.2 * p.1)) = _
    rw [Summable.tsum_sub (S.summable_correction p) ((S.summable_coefficient p.2).mul_right p.1),
      tsum_mul_right, S.tsum_coefficient]
  rw [hrewrite] at hcor
  have hc : |(S.excess 0 p.2 - δ) * p.1| ≤ δ / 4 := by
    have he : S.excess 0 p.2 - δ = Real.cos (S.Y 0 p.2) - Real.cos (latitude p.2) := by
      simp [excess, rate]
      ring
    rw [he, abs_mul]
    calc
      _ ≤ (rate δ 0 / (4 * Real.pi)) * Real.pi := by
        have hd := S.cos_error 0 p.2
        exact mul_le_mul hd (abs_le.mpr hx) (abs_nonneg p.1) ((abs_nonneg _).trans hd)
      _ = δ / 4 := by simp [rate]; field_simp
  have he := (S.excess_bounds 0 p.2).2
  simp [rate] at he
  have hrate : 0 ≤ δ := by simpa [rate] using (abs_nonneg _).trans (S.errorRateX 0 0)
  have hidentity : S.scalar p - (Real.cos p.2 + δ) * p.1 =
      ((∑' n, S.correctionTerm n p) - S.excess 0 p.2 * p.1) +
        (S.excess 0 p.2 - δ) * p.1 := by
    rw [scalar, longitude, latitude, clamp_eq hx, clamp_eq hy]
    ring
  rw [hidentity]
  exact (abs_add_le _ _).trans (by linarith)

def horizontalControl (x : ℝ) := ∑' n, (2 * rate δ n) * S.X n x

theorem horizontal_increment_bound (x x' y : ℝ) :
    |(∑' n, S.correctionTerm n (x', y)) - ∑' n, S.correctionTerm n (x, y)| ≤
      |S.horizontalControl x' - S.horizontalControl x| :=
  abs_tsum_weighted_sub_le ((summable_rate δ).mul_left 2) (fun n => S.coefficient_bounds n y)
    S.monoX S.boundX x x'

theorem rate_nonneg (S : Staircases δ) (n : ℕ) : 0 ≤ rate δ n :=
  (abs_nonneg _).trans (S.errorRateX n 0)

theorem abs_rate_le (S : Staircases δ) (n : ℕ) : |rate δ n| ≤ δ := by
  rw [abs_of_nonneg (S.rate_nonneg n)]
  exact mul_le_of_le_one_right (by simpa [rate] using S.rate_nonneg 0)
    (pow_le_one₀ (by norm_num) (by norm_num))

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
    have h1 := S.errorRateX n x
    have h2 := S.errorRateX (n + 1) x
    rw [rate_succ] at h2
    rcases abs_le.mp h1 with ⟨hl1, hu1⟩
    rcases abs_le.mp h2 with ⟨hl2, hu2⟩
    exact abs_le.mpr ⟨by linarith [S.rate_nonneg n], by linarith [S.rate_nonneg n]⟩

theorem summable_longitudeIncrement (x : ℝ) : Summable (fun n => S.longitudeIncrement n x) :=
  (summable_incrementWeight δ).of_norm_bounded (fun n => S.longitudeIncrement_bound n x)

theorem tsum_longitudeIncrement (x : ℝ) : (∑' n, S.longitudeIncrement n x) = longitude x := by
  have ht : Tendsto (fun n => S.X n x) atTop (𝓝 (longitude x)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 <|
      squeeze_zero (fun _ => norm_nonneg _) (fun n => S.errorRateX n x)
        (summable_rate δ).tendsto_atTop_zero
  exact GlobeFlattening.tsum_increment (A := fun n => S.longitudeStream n x) rfl
    (S.summable_longitudeIncrement x) ht

theorem scalar_series (x y : ℝ) :
    S.scalar (x, y) = ∑' n, (rate δ n + Real.cos (S.Y n y)) * S.longitudeIncrement n x := by
  have hE : Antitone (fun n => S.excess n y) :=
    antitone_nat_of_succ_le (fun n => sub_nonneg.mp (S.coefficient_bounds n y).1)
  have heq : (∑' n, S.correctionTerm n (x, y)) = ∑' n, S.excess n y * S.longitudeIncrement n x :=
    GlobeFlattening.tsum_weighted_increment_of_antitone (A := fun n => S.longitudeStream n x)
      rfl hE (S.summable_excess y).tendsto_atTop_zero (S.summable_longitudeIncrement x) (S.boundX · x)
  have hEbound (n : ℕ) : |S.excess n y| ≤ 2 * δ := by
    have h := S.excess_bounds n y
    rw [abs_of_nonneg (by linarith [S.rate_nonneg n, h.1])]
    linarith [h.2, (le_abs_self (rate δ n)).trans (S.abs_rate_le n),
      (by simpa [rate] using S.rate_nonneg 0 : 0 ≤ δ)]
  have hEΔ := summable_mul_of_abs_le (summable_incrementWeight δ) hEbound
    (fun n => S.longitudeIncrement_bound n x)
  have hbase := (S.summable_longitudeIncrement x).mul_left (Real.cos (latitude y))
  change longitude x * Real.cos (latitude y) + (∑' n, S.correctionTerm n (x, y)) = _
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
  singular_bounded_weighted_tsum S.X (fun n => 2 * rate δ n)
    (fun n => mul_nonneg (by norm_num) (S.rate_nonneg n))
    ((summable_rate δ).mul_left 2) (fun x => ⟨Real.pi, fun n => S.boundX n x⟩)
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
  let R := fun r => ∑' n, S.correctionTerm n r
  have h : S.scalar mid - S.scalar p - Real.cos p.2 * (q.1 - p.1) = R mid - R p := by
    have hx : p.1 ∈ Icc (-Real.pi) Real.pi := hp.1
    have hx' : q.1 ∈ Icc (-Real.pi) Real.pi := hq.1
    have hy : p.2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := hp.2
    simp only [scalar, longitude, latitude, mid, clamp_eq hx, clamp_eq hx', clamp_eq hy, R]
    ring
  rw [show S.scalar q - S.scalar p - Real.cos p.2 * (q.1 - p.1) =
    (R mid - R p) + (S.scalar q - S.scalar mid) by rw [← h]; ring]
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
    exact S.scalar_strictLowerSlope hδ hp.1 hq.1 hp.2 hlong
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
