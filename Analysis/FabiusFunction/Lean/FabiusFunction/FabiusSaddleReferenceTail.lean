import FabiusFunction.FabiusSaddleCentral

/-!
# Gaussian reference tails outside the central saddle interval

The Fabius saddle argument compares a rescaled saddle kernel `K` against the
reference

`exp (-v ^ 2 / 2) * (1 + (a * v + c * v ^ 3) * I)`,

a standard Gaussian plus the odd linear-plus-cubic correction
`oddCorrection a c` of `FabiusFunction.FabiusSaddleCentral`.  That module
bounds the `L¹` distance between kernel and reference on the central interval
`[-A, A]`.  This module supplies the complementary half, the integral over
`(Icc (-A) A)ᶜ`, so that the two estimates add up to a bound on the whole
line.

Every tail estimate here goes through one crude majorant: for `4 ≤ A` and
`A ≤ |v|` one has `-v ^ 2 / 2 + |v| ≤ -(A / 4) * |v|`, which turns a Gaussian
times a power into a pure exponential and yields

`∫_{|v| > A} exp (-v ^ 2 / 2) * |v| ^ k ≤ 8 * k! * exp (-A ^ 2 / 4) / A`.

At the standard radius `A = fabiusSaddleCentralRadius b = sqrt (32 * log b)`
this reads `exp (-A ^ 2 / 4) = b⁻¹ ^ 8`, comfortably past the `O(1 / b)` the
saddle argument asks for.  The slack is deliberate: a single radius then
serves the Gaussian and both odd coefficients at once.

## Main results

* `integral_gaussian_abs_pow_compl_Icc_le` -- the explicit `k`-th absolute
  moment tail `8 * k! * exp (-A ^ 2 / 4) / A`, for `4 ≤ A`.  Also reused by
  `FabiusFunction.GaussianPolynomialTail` for arbitrary-order polynomial
  references.
* `integral_norm_gaussian_add_oddCorrection_compl_Icc_le` -- the same estimate
  assembled for the Gaussian-plus-odd reference, with explicit constants `8`,
  `8 * |a|` and `48 * |c|` multiplying `exp (-A ^ 2 / 4) / A`.
* `integral_norm_gaussian_add_oddCorrection_standardRadius_isBigO` -- along a
  filter on which `b` tends to infinity and the coefficients obey
  `b * a ^ 2 ≤ Clinear ^ 2` and `b * c ^ 2 ≤ Ccubic ^ 2`, the reference tail at
  the standard radius is `O(1 / b)`.
* `integral_norm_sub_gaussian_add_oddCorrection_standardRadius_isBigO` -- the
  form consumers use: if the kernel `K` also has an `O(1 / b)` tail, then so
  does `K` minus the reference.  This is the outer-region input that
  `FabiusFunction.FabiusSaddleCentralLambert` combines with the central
  estimate to reach the normalized saddle kernel mass asymptotics.

The remaining declarations are private helpers: integrability of
`exp (-v ^ 2 / 2) * |v| ^ k`, the pointwise exponential majorant, the
evaluation of `exp (-A ^ 2 / 4)` at the standard radius, and the passage from
`b * a ^ 2 ≤ C ^ 2` to `|a| ≤ C / sqrt b`.

## Conventions and caveats

The hypothesis `4 ≤ A` is used in every bound and is not cosmetic; the
exponential majorant fails for small `A`.  The constants are sufficient, not
sharp: the true Gaussian tail decays like `exp (-A ^ 2 / 2)`, and the weaker
`exp (-A ^ 2 / 4)` is the price of absorbing the polynomial factor into the
exponential.  Coefficient bounds are phrased as `b * a ^ 2 ≤ Clinear ^ 2` to
match the central saddle theorem, although the proofs here only use the
weaker consequence `|a| ≤ Clinear`.  The odd correction is kept in the
reference rather than dropped: it has size `O(1 / sqrt b)`, too large to
discard at the accuracy sought, and keeping it is free because it integrates
to zero by oddness over the symmetric central interval.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Fabius
namespace SaddleCentral

private lemma gaussian_abs_pow_le_exp_tail
    (k : ℕ) {A v : ℝ} (hA : 4 ≤ A) (hv : A ≤ |v|) :
    Real.exp (-(v ^ 2) / 2) * |v| ^ k ≤
      k.factorial * Real.exp (-(A / 4) * |v|) := by
  have hu : 0 ≤ |v| := abs_nonneg v
  have hpow := Real.pow_div_factorial_le_exp |v| hu k
  have hpoly : |v| ^ k ≤ k.factorial * Real.exp |v| := by
    have hk : (0 : ℝ) < k.factorial := by positivity
    rw [div_le_iff₀ hk] at hpow
    simpa [mul_comm] using hpow
  have hexponent : -(v ^ 2) / 2 + |v| ≤ -(A / 4) * |v| := by
    have hv2 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
    rw [hv2]
    nlinarith [abs_nonneg v]
  calc
    Real.exp (-(v ^ 2) / 2) * |v| ^ k ≤
        Real.exp (-(v ^ 2) / 2) * (k.factorial * Real.exp |v|) := by
          gcongr
    _ = k.factorial * Real.exp (-(v ^ 2) / 2 + |v|) := by
      rw [Real.exp_add]
      ring
    _ ≤ k.factorial * Real.exp (-(A / 4) * |v|) := by gcongr

private lemma integrable_gaussian_abs_pow (k : ℕ) :
    Integrable (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * |v| ^ k) := by
  have h := integrable_gaussian_mul_pow k
  exact h.norm.congr <| by
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

lemma integral_gaussian_abs_pow_compl_Icc_le
    (k : ℕ) {A : ℝ} (hA : 4 ≤ A) :
    (∫ v in (Icc (-A) A)ᶜ,
      Real.exp (-(v ^ 2) / 2) * |v| ^ k) ≤
        8 * k.factorial * Real.exp (-(A ^ 2) / 4) / A := by
  have hA0 : 0 < A := by linarith
  have hlam : 0 < A / 4 := by positivity
  have hmajor := (integrable_exp_neg_mul_abs (A / 4) hlam).const_mul
    (k.factorial : ℝ)
  have hmono :
      (∫ v in (Icc (-A) A)ᶜ,
        Real.exp (-(v ^ 2) / 2) * |v| ^ k) ≤
      ∫ v in (Icc (-A) A)ᶜ,
        (k.factorial : ℝ) * Real.exp (-(A / 4) * |v|) := by
    apply setIntegral_mono_on (integrable_gaussian_abs_pow k).integrableOn
      hmajor.integrableOn measurableSet_Icc.compl
    intro v hv
    apply gaussian_abs_pow_le_exp_tail k hA
    rw [mem_compl_iff, mem_Icc] at hv
    by_cases hleft : -A ≤ v
    · have hright : A < v := by
        by_contra h
        exact hv ⟨hleft, le_of_not_gt h⟩
      exact (hright.trans_le (le_abs_self v)).le
    · have hvleft : v < -A := lt_of_not_ge hleft
      exact (lt_of_lt_of_le (by linarith : A < -v) (neg_le_abs v)).le
  calc
    (∫ v in (Icc (-A) A)ᶜ,
        Real.exp (-(v ^ 2) / 2) * |v| ^ k) ≤
      ∫ v in (Icc (-A) A)ᶜ,
        (k.factorial : ℝ) * Real.exp (-(A / 4) * |v|) := hmono
    _ = k.factorial * (2 * Real.exp (-(A / 4) * A) / (A / 4)) := by
      rw [integral_const_mul,
        integral_exp_neg_mul_abs_compl_Icc (A / 4) A hlam hA0.le]
    _ = 8 * k.factorial * Real.exp (-(A ^ 2) / 4) / A := by
      field_simp [hA0.ne']
      ring_nf

private lemma integrable_gaussian_abs_pow_mul_const (k : ℕ) (c : ℝ) :
    Integrable (fun v : ℝ => c *
      (Real.exp (-(v ^ 2) / 2) * |v| ^ k)) :=
  (integrable_gaussian_abs_pow k).const_mul c

lemma integral_norm_gaussian_add_oddCorrection_compl_Icc_le
    (a c : ℝ) {A : ℝ} (hA : 4 ≤ A) :
    (∫ v in (Icc (-A) A)ᶜ,
      ‖QuantitativeSaddle.standardGaussian v + oddCorrection a c v‖) ≤
        8 * Real.exp (-(A ^ 2) / 4) / A +
        |a| * (8 * Real.exp (-(A ^ 2) / 4) / A) +
        |c| * (48 * Real.exp (-(A ^ 2) / 4) / A) := by
  let g : ℝ → ℝ := fun v => Real.exp (-(v ^ 2) / 2)
  let major : ℝ → ℝ := fun v =>
    g v + |a| * (g v * |v|) + |c| * (g v * |v| ^ 3)
  have href : Integrable
      (fun v => ‖QuantitativeSaddle.standardGaussian v + oddCorrection a c v‖) :=
    (QuantitativeSaddle.integrable_standardGaussian.add
      (integrable_oddCorrection a c)).norm
  have hmajor : Integrable major := by
    have h0 := integrable_gaussian_abs_pow 0
    have h1 := integrable_gaussian_abs_pow_mul_const 1 |a|
    have h3 := integrable_gaussian_abs_pow_mul_const 3 |c|
    apply (h0.add h1 |>.add h3).congr
    filter_upwards with v
    dsimp [major, g]
    norm_num
  have hpoint : ∀ v : ℝ,
      ‖QuantitativeSaddle.standardGaussian v + oddCorrection a c v‖ ≤ major v := by
    intro v
    have hnormG : ‖QuantitativeSaddle.standardGaussian v‖ = g v := by
      unfold QuantitativeSaddle.standardGaussian g
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    calc
      ‖QuantitativeSaddle.standardGaussian v + oddCorrection a c v‖ ≤
          ‖QuantitativeSaddle.standardGaussian v‖ + ‖oddCorrection a c v‖ :=
        norm_add_le _ _
      _ = g v + g v * |a * v + c * v ^ 3| := by
        rw [hnormG, oddCorrection, norm_mul, hnormG, norm_oddPhase]
      _ ≤ g v + |a| * (g v * |v|) + |c| * (g v * |v| ^ 3) := by
        have hg : 0 ≤ g v := by dsimp [g]; positivity
        calc
          g v + g v * |a * v + c * v ^ 3| ≤
              g v + g v * (|a * v| + |c * v ^ 3|) := by
            gcongr
            exact abs_add_le _ _
          _ = _ := by
            rw [abs_mul, abs_mul, abs_pow]
            ring
      _ = major v := rfl
  have hmono :
      (∫ v in (Icc (-A) A)ᶜ,
        ‖QuantitativeSaddle.standardGaussian v + oddCorrection a c v‖) ≤
          ∫ v in (Icc (-A) A)ᶜ, major v :=
    setIntegral_mono_on href.integrableOn hmajor.integrableOn
      measurableSet_Icc.compl (fun v _ => hpoint v)
  have h0 := integral_gaussian_abs_pow_compl_Icc_le 0 hA
  have h1 := integral_gaussian_abs_pow_compl_Icc_le 1 hA
  have h3 := integral_gaussian_abs_pow_compl_Icc_le 3 hA
  have hg : Integrable g := by
    simpa [g] using integrable_gaussian_abs_pow 0
  have haint : Integrable (fun v => |a| * (g v * |v|)) := by
    simpa [g] using integrable_gaussian_abs_pow_mul_const 1 |a|
  have hcint : Integrable (fun v => |c| * (g v * |v| ^ 3)) := by
    simpa [g] using integrable_gaussian_abs_pow_mul_const 3 |c|
  calc
    (∫ v in (Icc (-A) A)ᶜ,
      ‖QuantitativeSaddle.standardGaussian v + oddCorrection a c v‖) ≤
        ∫ v in (Icc (-A) A)ᶜ, major v := hmono
    _ = (∫ v in (Icc (-A) A)ᶜ, g v) +
        |a| * (∫ v in (Icc (-A) A)ᶜ, g v * |v|) +
        |c| * (∫ v in (Icc (-A) A)ᶜ, g v * |v| ^ 3) := by
      calc
        (∫ v in (Icc (-A) A)ᶜ,
            g v + |a| * (g v * |v|) + |c| * (g v * |v| ^ 3)) =
            (∫ v in (Icc (-A) A)ᶜ, g v + |a| * (g v * |v|)) +
              ∫ v in (Icc (-A) A)ᶜ, |c| * (g v * |v| ^ 3) := by
          simpa only [Pi.add_apply] using
            (integral_add (hg.add haint).integrableOn hcint.integrableOn)
        _ = ((∫ v in (Icc (-A) A)ᶜ, g v) +
              ∫ v in (Icc (-A) A)ᶜ, |a| * (g v * |v|)) +
              ∫ v in (Icc (-A) A)ᶜ, |c| * (g v * |v| ^ 3) := by
          congr 1
          simpa only [Pi.add_apply] using
            (integral_add hg.integrableOn haint.integrableOn)
        _ = _ := by rw [integral_const_mul, integral_const_mul]
    _ ≤ 8 * Real.exp (-(A ^ 2) / 4) / A +
        |a| * (8 * Real.exp (-(A ^ 2) / 4) / A) +
        |c| * (48 * Real.exp (-(A ^ 2) / 4) / A) := by
      dsimp [g]
      norm_num at h0 h1 h3
      gcongr

private lemma exp_neg_sq_centralRadius_div_four
    {b : ℝ} (hb : 1 ≤ b) :
    Real.exp (-(fabiusSaddleCentralRadius b ^ 2) / 4) = b⁻¹ ^ 8 := by
  rw [sq_fabiusSaddleCentralRadius hb]
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  rw [show -(32 * Real.log b) / 4 = -(8 * Real.log b) by ring,
    Real.exp_neg, show Real.exp (8 * Real.log b) = b ^ 8 by
      calc
        Real.exp (8 * Real.log b) = Real.exp (Real.log b) ^ 8 := by
          simpa using Real.exp_nat_mul (Real.log b) 8
        _ = b ^ 8 := by rw [Real.exp_log hb0]]
  rw [inv_pow]

private lemma coeff_abs_le_div_sqrt
    {b a C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (h : b * a ^ 2 ≤ C ^ 2) : |a| ≤ C / Real.sqrt b := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  rw [le_div_iff₀ hs]
  have hs2 : (Real.sqrt b * |a|) ^ 2 = b * a ^ 2 := by
    rw [mul_pow, sq_abs, Real.sq_sqrt hb.le]
  nlinarith [sq_nonneg (Real.sqrt b * |a| - C)]

/-- The Gaussian plus the necessary odd correction has an `O(1/b)` tail at
the standard radius, uniformly under the coefficient bounds consumed by the
central saddle theorem. -/
theorem integral_norm_gaussian_add_oddCorrection_standardRadius_isBigO
    {α : Type*} (l : Filter α) (b a c : α → ℝ)
    (Clinear Ccubic : ℝ) (hClinear : 0 ≤ Clinear) (hCcubic : 0 ≤ Ccubic)
    (hbinfty : Tendsto b l atTop)
    (ha : ∀ᶠ i in l, b i * (a i) ^ 2 ≤ Clinear ^ 2)
    (hc : ∀ᶠ i in l, b i * (c i) ^ 2 ≤ Ccubic ^ 2) :
    (fun i => ∫ v in (Icc (-fabiusSaddleCentralRadius (b i))
        (fabiusSaddleCentralRadius (b i)))ᶜ,
      ‖QuantitativeSaddle.standardGaussian v + oddCorrection (a i) (c i) v‖)
      =O[l] (fun i => (b i)⁻¹) := by
  let C : ℝ := 8 + 8 * Clinear + 48 * Ccubic
  apply IsBigO.of_bound C
  filter_upwards [hbinfty.eventually_ge_atTop (Real.exp 1), ha, hc] with i hb hai hci
  have hb1 : 1 ≤ b i := by
    exact (by have := Real.exp_one_gt_d9; linarith : (1 : ℝ) ≤ Real.exp 1).trans hb
  have hb0 : 0 < b i := zero_lt_one.trans_le hb1
  have hA : 4 ≤ fabiusSaddleCentralRadius (b i) := by
    unfold fabiusSaddleCentralRadius
    have hlog0 : 0 ≤ Real.log (b i) := Real.log_nonneg hb1
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have hlog : 1 ≤ Real.log (b i) :=
      (Real.le_log_iff_exp_le hb0).2 hb
    nlinarith
  have ha' := coeff_abs_le_div_sqrt hb0 hClinear hai
  have hc' := coeff_abs_le_div_sqrt hb0 hCcubic hci
  have htail := integral_norm_gaussian_add_oddCorrection_compl_Icc_le
    (a i) (c i) hA
  rw [exp_neg_sq_centralRadius_div_four hb1] at htail
  have hsqrt1 : 1 ≤ Real.sqrt (b i) := Real.one_le_sqrt.mpr hb1
  have hcoeffA : |a i| ≤ Clinear :=
    ha'.trans (div_le_self hClinear hsqrt1)
  have hcoeffC : |c i| ≤ Ccubic :=
    hc'.trans (div_le_self hCcubic hsqrt1)
  have hA1 : 1 ≤ fabiusSaddleCentralRadius (b i) := hA.trans' (by norm_num)
  have hinvA : (fabiusSaddleCentralRadius (b i))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hA1
  have hbInv0 : 0 ≤ (b i)⁻¹ := by positivity
  have hbInv1 : (b i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1
  have hintegral0 : 0 ≤ (∫ v in (Icc (-fabiusSaddleCentralRadius (b i))
      (fabiusSaddleCentralRadius (b i)))ᶜ,
      ‖QuantitativeSaddle.standardGaussian v + oddCorrection (a i) (c i) v‖) :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hintegral0,
    abs_of_nonneg hbInv0]
  calc
    (∫ v in (Icc (-fabiusSaddleCentralRadius (b i))
        (fabiusSaddleCentralRadius (b i)))ᶜ,
      ‖QuantitativeSaddle.standardGaussian v + oddCorrection (a i) (c i) v‖) ≤
        8 * (b i)⁻¹ ^ 8 / fabiusSaddleCentralRadius (b i) +
          |a i| * (8 * (b i)⁻¹ ^ 8 / fabiusSaddleCentralRadius (b i)) +
          |c i| * (48 * (b i)⁻¹ ^ 8 / fabiusSaddleCentralRadius (b i)) := htail
    _ ≤ C * (b i)⁻¹ := by
      dsimp [C]
      have hpow : (b i)⁻¹ ^ 8 ≤ (b i)⁻¹ := by
        calc
          (b i)⁻¹ ^ 8 = (b i)⁻¹ * (b i)⁻¹ ^ 7 := by ring
          _ ≤ (b i)⁻¹ * 1 := by
            gcongr
            exact pow_le_one₀ hbInv0 hbInv1
          _ = (b i)⁻¹ := mul_one _
      have hbase : (b i)⁻¹ ^ 8 / fabiusSaddleCentralRadius (b i) ≤ (b i)⁻¹ := by
        rw [div_eq_mul_inv]
        exact (mul_le_of_le_one_right (by positivity) hinvA).trans hpow
      have hbase0 : 0 ≤ (b i)⁻¹ ^ 8 /
          fabiusSaddleCentralRadius (b i) := by positivity
      calc
        8 * (b i)⁻¹ ^ 8 / fabiusSaddleCentralRadius (b i) +
              |a i| * (8 * (b i)⁻¹ ^ 8 / fabiusSaddleCentralRadius (b i)) +
              |c i| * (48 * (b i)⁻¹ ^ 8 / fabiusSaddleCentralRadius (b i)) =
            (8 + 8 * |a i| + 48 * |c i|) *
              ((b i)⁻¹ ^ 8 / fabiusSaddleCentralRadius (b i)) := by ring
        _ ≤ (8 + 8 * Clinear + 48 * Ccubic) * (b i)⁻¹ := by
          gcongr

/-- If a saddle kernel and the Gaussian-plus-odd reference each have an
`O(1/b)` complementary tail, then so does their difference. -/
theorem integral_norm_sub_gaussian_add_oddCorrection_standardRadius_isBigO
    {α : Type*} (l : Filter α) (b a c : α → ℝ) (K : α → ℝ → ℂ)
    (Clinear Ccubic : ℝ) (hClinear : 0 ≤ Clinear) (hCcubic : 0 ≤ Ccubic)
    (hbinfty : Tendsto b l atTop)
    (ha : ∀ᶠ i in l, b i * (a i) ^ 2 ≤ Clinear ^ 2)
    (hc : ∀ᶠ i in l, b i * (c i) ^ 2 ≤ Ccubic ^ 2)
    (hKint : ∀ᶠ i in l, Integrable (K i))
    (hKtail :
      (fun i => ∫ v in (Icc (-fabiusSaddleCentralRadius (b i))
          (fabiusSaddleCentralRadius (b i)))ᶜ, ‖K i v‖) =O[l]
        (fun i => (b i)⁻¹)) :
    (fun i => ∫ v in (Icc (-fabiusSaddleCentralRadius (b i))
        (fabiusSaddleCentralRadius (b i)))ᶜ,
      ‖K i v - (QuantitativeSaddle.standardGaussian v +
        oddCorrection (a i) (c i) v)‖) =O[l]
      (fun i => (b i)⁻¹) := by
  let reference : α → ℝ → ℂ := fun i v =>
    QuantitativeSaddle.standardGaussian v + oddCorrection (a i) (c i) v
  let central : α → Set ℝ := fun i =>
    Icc (-fabiusSaddleCentralRadius (b i))
      (fabiusSaddleCentralRadius (b i))
  let Ktail : α → ℝ := fun i => ∫ v in (central i)ᶜ, ‖K i v‖
  let Rtail : α → ℝ := fun i => ∫ v in (central i)ᶜ, ‖reference i v‖
  let Dtail : α → ℝ := fun i => ∫ v in (central i)ᶜ,
    ‖K i v - reference i v‖
  have hRint : ∀ i, Integrable (reference i) := fun i =>
    QuantitativeSaddle.integrable_standardGaussian.add
      (integrable_oddCorrection (a i) (c i))
  have hRtail : Rtail =O[l] (fun i => (b i)⁻¹) := by
    simpa only [Rtail, reference, central] using
      integral_norm_gaussian_add_oddCorrection_standardRadius_isBigO
        l b a c Clinear Ccubic hClinear hCcubic hbinfty ha hc
  have hKtail' : Ktail =O[l] (fun i => (b i)⁻¹) := by
    simpa only [Ktail, central] using hKtail
  have hdom : Dtail =O[l] (fun i => Ktail i + Rtail i) := by
    apply IsBigO.of_bound 1
    filter_upwards [hKint] with i hKi
    have hRi := hRint i
    have hdiffInt : Integrable (fun v => ‖K i v - reference i v‖) :=
      (hKi.sub hRi).norm
    have hsumInt : Integrable (fun v => ‖K i v‖ + ‖reference i v‖) :=
      hKi.norm.add hRi.norm
    have hmono : Dtail i ≤ Ktail i + Rtail i := by
      dsimp only [Dtail, Ktail, Rtail]
      calc
        (∫ v in (central i)ᶜ, ‖K i v - reference i v‖) ≤
            ∫ v in (central i)ᶜ, (‖K i v‖ + ‖reference i v‖) := by
          apply setIntegral_mono_on hdiffInt.integrableOn hsumInt.integrableOn
            measurableSet_Icc.compl
          intro v _
          exact norm_sub_le _ _
        _ = (∫ v in (central i)ᶜ, ‖K i v‖) +
            ∫ v in (central i)ᶜ, ‖reference i v‖ := by
          simpa only [Pi.add_apply] using
            (integral_add hKi.norm.integrableOn hRi.norm.integrableOn)
    have hD0 : 0 ≤ Dtail i := integral_nonneg fun _ => norm_nonneg _
    have hsum0 : 0 ≤ Ktail i + Rtail i := add_nonneg
      (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD0,
      abs_of_nonneg hsum0, one_mul]
    exact hmono
  have hsum : (fun i => Ktail i + Rtail i) =O[l] (fun i => (b i)⁻¹) :=
    hKtail'.add hRtail
  simpa only [Dtail, reference, central] using hdom.trans hsum

end SaddleCentral
end Fabius
