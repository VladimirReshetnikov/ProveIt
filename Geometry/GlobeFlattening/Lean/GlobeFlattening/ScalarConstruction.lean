import GlobeFlattening.CoordinateRectangles
import GlobeFlattening.SingularSeries
import GlobeFlattening.SingularStaircase
import GlobeFlattening.StaircaseEstimates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The scalar longitude coordinate from singular staircases

Approximate longitude and latitude with the same monotone singular
staircases `X n`. The correction weights are successive drops
of `rate n + cos (X n y)`. Their positivity gives the strict lower
longitude slope.

The scalar coordinate is the sinusoidal coordinate plus the
longitude correction. Summation by parts shows that finite sums of
longitude increments weighted by `rate n + cos (X n y)` converge to the same
coordinate. The two formulas bound horizontal and vertical errors by a
single monotone singular sum applied to both coordinates.
-/

namespace GlobeFlattening

open Filter Set MeasureTheory
open scoped NNReal Topology

noncomputable section

def rate (δ : ℝ) (n : ℕ) := δ * (1 / 2 : ℝ)^n

private theorem rate_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < rate δ n := by
  unfold rate
  positivity

theorem rate_succ (δ : ℝ) (n : ℕ) : rate δ (n + 1) = rate δ n / 2 := by
  simp [rate, pow_succ, mul_assoc, div_eq_mul_inv]

theorem hasSum_rate (δ : ℝ) : HasSum (rate δ) (δ * 2) := hasSum_geometric_two.mul_left δ

theorem summable_rate (δ : ℝ) : Summable (rate δ) := (hasSum_rate δ).summable

structure Staircases (δ : ℝ) where
  delta_pos : 0 < δ
  X : ℕ → ℝ → ℝ
  monoX : ∀ n, Monotone (X n)
  continuousX : ∀ n, Continuous (X n)
  singularX : ∀ n, ∀ᵐ x ∂volume, HasDerivAt (X n) 0 x
  boundX : ∀ n x, |X n x| ≤ Real.pi
  stepX : ∀ n x, |X (n + 1) x - X n x| < rate δ (n + 1)
  tendsto_X : ∀ x ∈ Icc (-Real.pi) Real.pi, Tendsto (fun n => X n x) atTop (𝓝 x)

theorem exists_staircases {δ : ℝ} (hδ : 0 < δ) : Nonempty (Staircases δ) := by
  have hX (n : ℕ) := exists_singular_approx (neg_lt_self Real.pi_pos) (rate_pos hδ (n + 2))
  choose X hc hm hr he hd using hX
  refine ⟨⟨hδ, X, hm, hc, hd, fun n x => abs_le.mpr (hr n x), ?_, ?_⟩⟩
  · intro n x
    have h := dist_triangle_right (X (n + 1) x) (X n x) (max (-Real.pi) (min Real.pi x))
    simp only [Real.dist_eq] at h
    linarith only [h, he (n + 1) x, he n x, rate_succ δ (n + 1), rate_succ δ (n + 2),
      rate_pos hδ (n + 1)]
  · intro x hx
    refine tendsto_iff_norm_sub_tendsto_zero.2 <|
      squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
        ((summable_rate δ).tendsto_atTop_zero.comp (tendsto_add_atTop_nat 2))
    simpa only [Function.comp_apply, Real.norm_eq_abs, min_eq_right hx.2, max_eq_right hx.1] using he n x

namespace Staircases

variable {δ : ℝ} (S : Staircases δ)

private def latitudeWeight (δ : ℝ) (n : ℕ) (t : ℝ) := rate δ n + Real.cos t

def latitudeProfile (n : ℕ) (y : ℝ) : ℝ := latitudeWeight δ n (S.X n y)
def coefficient (n : ℕ) (y : ℝ) : ℝ := S.latitudeProfile n y - S.latitudeProfile (n + 1) y

theorem coefficient_bounds (n : ℕ) (y : ℝ) :
    0 < S.coefficient n y ∧ |S.coefficient n y| ≤ rate δ n := by
  have hcos := abs_lt.mp <| (Real.abs_cos_sub_cos_le _ _).trans_lt (S.stepX n y)
  unfold coefficient latitudeProfile latitudeWeight
  rw [rate_succ] at hcos ⊢
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    linarith only [hcos.1, hcos.2]

def correction (p : ℝ × ℝ) := ∑' n, S.coefficient n p.2 * S.X n p.1

private theorem norm_correction_term (n : ℕ) (p : ℝ × ℝ) :
    ‖S.coefficient n p.2 * S.X n p.1‖ ≤ rate δ n * Real.pi :=
  norm_mul_le_of_le (S.coefficient_bounds n p.2).2 (S.boundX n p.1)

private theorem correction_series :
    Continuous S.correction ∧ (∀ p, HasSum (fun n => S.coefficient n p.2 * S.X n p.1) (S.correction p)) := by
  have hu := tendstoUniformly_tsum ((summable_rate δ).mul_right Real.pi) S.norm_correction_term
  refine ⟨hu.continuous (Frequently.of_forall fun N => continuous_finsetSum N fun n _ => ?_), hu.tendsto_at⟩
  have hprofile (k : ℕ) : Continuous (S.latitudeProfile k) :=
    continuous_const.add (Real.continuous_cos.comp (S.continuousX k))
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
    exact (S.stepX n x).le.trans (rate_le_rate_add_pi δ _)

def scalar (p : ℝ × ℝ) := p.1 * Real.cos p.2 + S.correction p

private theorem tendsto_increment_sum {p : ℝ × ℝ} (hp : p ∈ sphereClosedBox) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, S.longitudeIncrement n p.1 * S.latitudeProfile n p.2)
      atTop (𝓝 (S.scalar p)) := by
  have hy : p.2 ∈ Icc (-Real.pi) Real.pi :=
    Icc_subset_Icc (neg_le_neg (half_le_self Real.pi_pos.le)) (half_le_self Real.pi_pos.le) hp.2
  have hprofile := (summable_rate δ).tendsto_atTop_zero.add
    ((Real.continuous_cos.tendsto _).comp (S.tendsto_X p.2 hy))
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  simpa only [Finset.sum_range_succ', longitudeIncrement, scalar, latitudeProfile, latitudeWeight,
    Function.comp_def, zero_add] using
    tendsto_sum_weighted_increment (S.correction_series.2 p) ((S.tendsto_X p.1 hp.1).mul hprofile)

theorem scalar_strictLowerSlope : StrictLowerSlopeOn S.scalar Real.cos sphereClosedBox := by
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq rfl hxx'
  obtain ⟨n, hX⟩ := ((S.tendsto_X x hp.1).eventually_lt (S.tendsto_X x' hq.1) hxx').exists
  have hsum : S.correction (x, y) < S.correction (x', y) :=
    hasSum_lt
      (fun k => mul_le_mul_of_nonneg_left (S.monoX k hxx'.le) (S.coefficient_bounds k y).1.le)
      (mul_lt_mul_of_pos_left hX (S.coefficient_bounds n y).1)
      (S.correction_series.2 (x, y)) (S.correction_series.2 (x', y))
  simp only [scalar]
  linarith only [hsum]

theorem scalar_error (p : ℝ × ℝ) :
    dist (flattenCoordinates S.scalar p) (sinusoidalCoordinates p) ≤ δ * 2 * Real.pi := by
  rw [dist_flattenCoordinates_sinusoidalCoordinates, scalar, add_sub_cancel_left, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded ((hasSum_rate δ).mul_right Real.pi) (S.norm_correction_term · p)

def horizontalControl (x : ℝ) := ∑' n, rate (δ + Real.pi) n * S.X n x

theorem linearization_bound (hcontrol : ∀ t, Summable (fun n => rate (δ + Real.pi) n * S.X n t))
    {p q : ℝ × ℝ} (hp : p ∈ sphereClosedBox) (hq : q ∈ sphereClosedBox) :
    |S.scalar q - S.scalar p - Real.cos p.2 * (q.1 - p.1)| ≤
      |S.horizontalControl q.1 - S.horizontalControl p.1| +
        |S.horizontalControl q.2 - S.horizontalControl p.2| := by
  let mid := (q.1, p.2)
  have hhorizontal := abs_sub_le_of_tendsto_weighted_comp (X := S.X) (f := fun _ => id) hcontrol
    (fun n => (S.coefficient_bounds n p.2).2.trans (rate_le_rate_add_pi δ n)) S.monoX
    (fun _ _ _ => le_rfl) p.1 q.1 (S.correction_series.2 p).tendsto_sum_nat (S.correction_series.2 mid).tendsto_sum_nat
  have hvertical := abs_sub_le_of_tendsto_weighted_comp (X := S.X) (f := latitudeWeight δ) hcontrol
    (fun n => S.longitudeIncrement_bound n q.1) S.monoX (fun _ x y => by
      simpa only [latitudeWeight, add_sub_add_left_eq_sub] using Real.abs_cos_sub_cos_le y x)
    p.2 q.2 (S.tendsto_increment_sum (p := mid) ⟨hq.1, hp.2⟩) (S.tendsto_increment_sum hq)
  calc
    _ = |(S.correction mid - S.correction p) + (S.scalar q - S.scalar mid)| := congrArg abs (by
      simp only [scalar, mid]
      ring)
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hhorizontal hvertical)

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
  obtain ⟨S⟩ := exists_staircases hδ
  obtain ⟨hcontrol, hsingular⟩ := summable_and_singular_weighted_tsum S.X (rate (δ + Real.pi))
    (fun n => (rate_pos (add_pos hδ Real.pi_pos) n).le)
    (summable_rate (δ + Real.pi)) S.boundX S.continuousX S.monoX S.singularX
  obtain ⟨E, hm, hsub, hnull, hderiv⟩ :=
    exists_hasFDerivAt_of_increment_bounds S.horizontalControl (fun p => Real.cos p.2)
      isOpen_sphereLongitudeDomain hsingular (fun p hp q hq =>
        S.linearization_bound hcontrol (sphereLongitudeDomain_subset_box hp) (sphereLongitudeDomain_subset_box hq))
  exact ⟨S.scalar, E, ((continuous_fst.mul (Real.continuous_cos.comp continuous_snd)).add
    S.correction_series.1).continuousOn, hm, hsub, hnull,
    fun q _ => (S.scalar_error q).trans_eq (by simp [δ, mul_assoc, Real.pi_ne_zero]),
    S.scalar_strictLowerSlope, hderiv⟩

end
end GlobeFlattening
