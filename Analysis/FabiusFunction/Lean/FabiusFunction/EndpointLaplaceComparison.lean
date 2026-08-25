import FabiusFunction.DyadicSharpDecomposition
import FabiusFunction.ProbabilityRepresentation
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Endpoint moments versus the negative Laplace transform

This module supplies the real-variable comparison needed to pass from the
Fabius endpoint moment `halfMoment n` to the negative Laplace transform at
scale `n`.

Its main ingredients are:

* a pointwise second-order comparison of `(1 - x)^n` with
  `exp (-n*x) * (1 - n*x^2/2)` on `[0,1]`;
* a Fubini/CDF bridge identifying integrals against the weighted-sum law with
  the survival-function moments from `LaplaceMoments`;
* a quantitative local logarithm lemma; and
* an `O(1/n)` transfer theorem whose remaining hypotheses are precisely the
  normalized tilted third/fourth-moment estimates supplied by the sharp
  periodic/saddle analysis.

The explicit logarithmic correction is

`n/2 * (negativeLaplaceLogSecond F n + negativeLaplaceLogFirst F n ^ 2)`,

which is `n/2` times the normalized second tilted moment.

The probability bridge also records the survival identity on the full
nonnegative ray and separates reflection invariance from the zero-tilt and
degree-zero moment normalizations.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Fabius

lemma abs_log_one_sub_second_remainder_le {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |Real.log (1 - x) + x + x ^ 2 / 2| ≤ 2 * x ^ 3 / 3 := by
  have hxlt : x < 1 := hx.trans_lt (by norm_num)
  have hnorm : ‖(-(x : ℂ))‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] using hxlt
  have h := Complex.norm_log_sub_logTaylor_le 2 hnorm
  have hpos : 0 ≤ 1 - x := by linarith
  have hden : 0 < 1 - x := by linarith
  have hcast :
      ((Real.log (1 - x) + x + x ^ 2 / 2 : ℝ) : ℂ) =
        Complex.log (1 + (-(x : ℂ))) - Complex.logTaylor 3 (-(x : ℂ)) := by
    rw [show 1 + (-(x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log hpos]
    simp [Complex.logTaylor_succ, Complex.logTaylor_zero]
    ring
  norm_num at h
  calc
    |Real.log (1 - x) + x + x ^ 2 / 2| =
        ‖((Real.log (1 - x) + x + x ^ 2 / 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖Complex.log (1 + (-(x : ℂ))) -
        Complex.logTaylor 3 (-(x : ℂ))‖ := by rw [hcast]
    _ ≤ ‖(-(x : ℂ))‖ ^ 3 * (1 - ‖(-(x : ℂ))‖)⁻¹ / 3 := by
      simpa using h
    _ ≤ 2 * x ^ 3 / 3 := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
      have hinv : (1 - x)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
        norm_num
        linarith
      calc
        x ^ 3 * (1 - x)⁻¹ / 3 ≤ x ^ 3 * 2 / 3 := by
          apply div_le_div_of_nonneg_right
          exact mul_le_mul_of_nonneg_left hinv (pow_nonneg hx0 3)
          norm_num
        _ = 2 * x ^ 3 / 3 := by ring

lemma abs_exp_neg_sub_one_add_le_sq (u : ℝ) (hu : 0 ≤ u) :
    |Real.exp (-u) - (1 - u)| ≤ u ^ 2 := by
  by_cases hu1 : u ≤ 1
  · have habs : |-u| ≤ 1 := by rw [abs_of_nonpos (neg_nonpos.mpr hu)]; linarith
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (Real.abs_exp_sub_one_sub_id_le habs)
  · have hu1' : 1 < u := lt_of_not_ge hu1
    have he0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
    have he1 : Real.exp (-u) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith)]
    nlinarith

lemma abs_exp_sub_exp_le_abs_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · have hba : b ≤ a := le_of_not_ge hab
    simpa [abs_sub_comm] using this hb ha hba
  have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
  have he : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonpos (sub_nonpos.mpr hab)]
  have hfac : Real.exp b - Real.exp a =
      Real.exp b * (1 - Real.exp (-(b - a))) := by
    rw [show a = b + (-(b - a)) by ring, Real.exp_add]
    ring
  have hfactor : Real.exp b ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hb
  have hsub0 : 0 ≤ 1 - Real.exp (-(b - a)) := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsub : 1 - Real.exp (-(b - a)) ≤ b - a := by
    linarith [Real.one_sub_le_exp_neg (b - a)]
  calc
    -(Real.exp a - Real.exp b) = Real.exp b - Real.exp a := by ring
    _ = Real.exp b * (1 - Real.exp (-(b - a))) := hfac
    _ ≤
        1 * (1 - Real.exp (-(b - a))) :=
      mul_le_mul_of_nonneg_right hfactor hsub0
    _ ≤ b - a := by simpa using hsub
    _ = -(a - b) := by ring

/-- A quantitative logarithm-transfer lemma.  If `m / b` is within `ε` of
`1 - a` and is itself within `1 / 2` of `1`, then passing to logarithms costs
at most the square of the relative displacement. -/
lemma abs_log_sub_log_add_le_sq_add {m b a ε : ℝ}
    (hm : 0 < m) (hb : 0 < b)
    (hsmall : |m / b - 1| ≤ 1 / 2)
    (happrox : |m / b - (1 - a)| ≤ ε) :
    |Real.log m - Real.log b + a| ≤ (m / b - 1) ^ 2 + ε := by
  let d : ℝ := m / b - 1
  have hd : |d| ≤ 1 / 2 := hsmall
  have hdlt : |d| < 1 := hd.trans_lt (by norm_num)
  have hratio : 0 < m / b := div_pos hm hb
  have hone : 0 < 1 + d := by
    dsimp [d]
    linarith
  have hlog : Real.log m - Real.log b = Real.log (1 + d) := by
    rw [← Real.log_div hm.ne' hb.ne']
    congr 1
    dsimp [d]
    ring
  have hrem : |Real.log (1 + d) - d| ≤ d ^ 2 := by
    have hnorm : ‖(d : ℂ)‖ < 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hdlt
    have hc := Complex.norm_log_one_add_sub_self_le hnorm
    have hcast :
        ((Real.log (1 + d) - d : ℝ) : ℂ) =
          Complex.log (1 + (d : ℂ)) - (d : ℂ) := by
      rw [show 1 + (d : ℂ) = ((1 + d : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log hone.le]
      norm_num
    have hden : 0 < 1 - |d| := by linarith
    have hinv : (1 - |d|)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
      norm_num
      linarith
    calc
      |Real.log (1 + d) - d| =
          ‖((Real.log (1 + d) - d : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖Complex.log (1 + (d : ℂ)) - (d : ℂ)‖ := by rw [hcast]
      _ ≤ ‖(d : ℂ)‖ ^ 2 * (1 - ‖(d : ℂ)‖)⁻¹ / 2 := hc
      _ = |d| ^ 2 * (1 - |d|)⁻¹ / 2 := by
        simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |d| ^ 2 := by
        have hsq : 0 ≤ |d| ^ 2 := sq_nonneg |d|
        nlinarith [mul_le_mul_of_nonneg_left hinv hsq]
      _ = d ^ 2 := sq_abs d
  rw [hlog]
  have hda : |d + a| ≤ ε := by
    rw [show d + a = m / b - (1 - a) by dsimp [d]; ring]
    exact happrox
  calc
    |Real.log (1 + d) + a| =
        |(Real.log (1 + d) - d) + (d + a)| := by ring_nf
    _ ≤ |Real.log (1 + d) - d| + |d + a| := abs_add_le _ _
    _ ≤ d ^ 2 + ε := add_le_add hrem hda

/-- Convenient corollary of `abs_log_sub_log_add_le_sq_add` whose hypotheses
only mention the proposed correction `a` and relative error `ε`. -/
lemma abs_log_sub_log_add_le_two_sq_add {m b a ε : ℝ}
    (hm : 0 < m) (hb : 0 < b) (hε : 0 ≤ ε)
    (hsmall : |a| + ε ≤ 1 / 2)
    (happrox : |m / b - (1 - a)| ≤ ε) :
    |Real.log m - Real.log b + a| ≤ 2 * a ^ 2 + 2 * ε := by
  have hdelta : |m / b - 1| ≤ |a| + ε := by
    calc
      |m / b - 1| = |(m / b - (1 - a)) - a| := by ring_nf
      _ ≤ |m / b - (1 - a)| + |a| := abs_sub _ _
      _ ≤ ε + |a| := add_le_add happrox le_rfl
      _ = |a| + ε := add_comm _ _
  have hδsmall : |m / b - 1| ≤ 1 / 2 := hdelta.trans hsmall
  have hεhalf : ε ≤ 1 / 2 := by
    nlinarith [abs_nonneg a]
  have hsq : (m / b - 1) ^ 2 ≤ 2 * a ^ 2 + ε := by
    have hsq' : (m / b - 1) ^ 2 ≤ (|a| + ε) ^ 2 := by
      rw [← sq_abs (m / b - 1)]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdelta
    rw [← sq_abs a]
    have hlin : 0 ≤ 1 - 2 * ε := by nlinarith
    nlinarith [sq_nonneg (|a| - ε), mul_nonneg hε hlin]
  exact (abs_log_sub_log_add_le_sq_add hm hb hδsmall happrox).trans <| by
    nlinarith

/-- Asymptotic logarithm transfer in a form independent of the particular
small parameter.  A relative approximation `m / b = 1 - a + O(ε)` becomes
`log m - log b = -a + O(h)` provided both `a²` and `ε` are `O(h)`. -/
theorem log_secondOrder_transfer_isBigO
    {α : Type*} (l : Filter α) (m b a ε h : α → ℝ)
    (hm : ∀ᶠ i in l, 0 < m i)
    (hb : ∀ᶠ i in l, 0 < b i)
    (hε0 : ∀ᶠ i in l, 0 ≤ ε i)
    (hsmall : ∀ᶠ i in l, |a i| + ε i ≤ 1 / 2)
    (happrox : ∀ᶠ i in l,
      |m i / b i - (1 - a i)| ≤ ε i)
    (ha_sq : (fun i ↦ (a i) ^ 2) =O[l] h)
    (hε : ε =O[l] h) :
    (fun i ↦ Real.log (m i) - Real.log (b i) + a i) =O[l] h := by
  have hpoint :
      (fun i ↦ Real.log (m i) - Real.log (b i) + a i) =O[l]
        (fun i ↦ 2 * (a i) ^ 2 + 2 * ε i) := by
    apply IsBigO.of_bound'
    filter_upwards [hm, hb, hε0, hsmall, happrox] with
      i hmi hbi hεi hs hi
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * (a i) ^ 2 + 2 * ε i)]
    exact abs_log_sub_log_add_le_two_sq_add hmi hbi hεi hs hi
  have hright : (fun i ↦ 2 * (a i) ^ 2 + 2 * ε i) =O[l] h := by
    simpa only using (ha_sq.const_mul_left 2).add (hε.const_mul_left 2)
  exact hpoint.trans hright

/-- The `n`th endpoint moment of a measure, restricted to the unit interval. -/
noncomputable def unitEndpointMoment (μ : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ x in Icc (0 : ℝ) 1, (1 - x) ^ n ∂μ

/-- The `k`th raw moment under the exponentially tilted unit-interval measure. -/
noncomputable def unitLaplaceMoment (μ : Measure ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  ∫ x in Icc (0 : ℝ) 1, Real.exp (-s * x) * x ^ k ∂μ

lemma unitLaplaceMoment_nonneg (μ : Measure ℝ) (s : ℝ) (k : ℕ) :
    0 ≤ unitLaplaceMoment μ s k := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg hx.1 k)

/-- Pointwise second-order comparison between an endpoint power and its Laplace kernel. -/
lemma abs_one_sub_pow_sub_exp_quadratic_le
    (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(1 - x) ^ n - Real.exp (-(n : ℝ) * x) *
        (1 - (n : ℝ) * x ^ 2 / 2)| ≤
      16 * Real.exp (-(n : ℝ) * x) *
        ((n : ℝ) * x ^ 3 + (n : ℝ) ^ 2 * x ^ 4) := by
  let N : ℝ := n
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  by_cases hxhalf : x ≤ 1 / 2
  · have hxlt : x < 1 := hxhalf.trans_lt (by norm_num)
    have hden : 0 < 1 - x := sub_pos.mpr hxlt
    let a : ℝ := N * (Real.log (1 - x) + x)
    let u : ℝ := N * x ^ 2 / 2
    have hu : 0 ≤ u := by positivity
    have ha : a ≤ 0 := by
      have hlog := Real.log_le_sub_one_of_pos hden
      dsimp [a]
      nlinarith
    have hbu : -u ≤ 0 := neg_nonpos.mpr hu
    have hexpdiff : |Real.exp a - Real.exp (-u)| ≤
        N * (2 * x ^ 3 / 3) := by
      refine (abs_exp_sub_exp_le_abs_of_nonpos ha hbu).trans ?_
      have hrem := abs_log_one_sub_second_remainder_le hx0 hxhalf
      have heq : a - -u = N * (Real.log (1 - x) + x + x ^ 2 / 2) := by
        dsimp [a, u]
        ring
      rw [heq, abs_mul, abs_of_nonneg hN0]
      exact mul_le_mul_of_nonneg_left hrem hN0
    have hexptaylor : |Real.exp (-u) - (1 - u)| ≤ u ^ 2 :=
      abs_exp_neg_sub_one_add_le_sq u hu
    have hnormalized : |Real.exp a - (1 - u)| ≤
        N * (2 * x ^ 3 / 3) + u ^ 2 := by
      calc
        |Real.exp a - (1 - u)| =
            |(Real.exp a - Real.exp (-u)) +
              (Real.exp (-u) - (1 - u))| := by ring_nf
        _ ≤ |Real.exp a - Real.exp (-u)| +
            |Real.exp (-u) - (1 - u)| := abs_add_le _ _
        _ ≤ N * (2 * x ^ 3 / 3) + u ^ 2 := add_le_add hexpdiff hexptaylor
    have hfactor : (1 - x) ^ n =
        Real.exp (-N * x) * Real.exp a := by
      rw [← Real.exp_log hden, ← Real.exp_nat_mul]
      dsimp [a, N]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfactor]
    change |Real.exp (-N * x) * Real.exp a -
        Real.exp (-N * x) * (1 - u)| ≤ _
    rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-N * x) * |Real.exp a - (1 - u)| ≤
          Real.exp (-N * x) * (N * (2 * x ^ 3 / 3) + u ^ 2) :=
        mul_le_mul_of_nonneg_left hnormalized (Real.exp_pos _).le
      _ ≤ 16 * Real.exp (-N * x) * (N * x ^ 3 + N ^ 2 * x ^ 4) := by
        have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx0 3
        have hx4 : 0 ≤ x ^ 4 := pow_nonneg hx0 4
        dsimp [u]
        nlinarith [mul_nonneg hN0 hx3, mul_nonneg (sq_nonneg N) hx4,
          Real.exp_pos (-N * x)]
  · have hxhalf' : 1 / 2 ≤ x := (lt_of_not_ge hxhalf).le
    have hbase0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    have hpow0 : 0 ≤ (1 - x) ^ n := pow_nonneg hbase0 n
    have hbasele : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
    have hpowle : (1 - x) ^ n ≤ Real.exp (-N * x) := by
      calc
        (1 - x) ^ n ≤ Real.exp (-x) ^ n :=
          pow_le_pow_left₀ hbase0 hbasele n
        _ = Real.exp (-N * x) := by
          rw [← Real.exp_nat_mul]
          dsimp [N]
          congr 1
          ring
    let u : ℝ := N * x ^ 2 / 2
    have hu : 0 ≤ u := by positivity
    have hraw : |(1 - x) ^ n - Real.exp (-N * x) * (1 - u)| ≤
        Real.exp (-N * x) * (2 + u) := by
      calc
        |(1 - x) ^ n - Real.exp (-N * x) * (1 - u)| ≤
            |(1 - x) ^ n| + |Real.exp (-N * x) * (1 - u)| := abs_sub _ _
        _ = (1 - x) ^ n + Real.exp (-N * x) * |1 - u| := by
          rw [abs_of_nonneg hpow0, abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (-N * x) + Real.exp (-N * x) * (1 + u) := by
          gcongr
          exact (abs_sub (1 : ℝ) u).trans_eq (by rw [abs_one, abs_of_nonneg hu])
        _ = Real.exp (-N * x) * (2 + u) := by ring
    change |(1 - x) ^ n - Real.exp (-N * x) * (1 - u)| ≤ _
    refine hraw.trans ?_
    have hx3lower : (1 / 2 : ℝ) ^ 3 ≤ x ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hxhalf' 3
    have hx2lower : (1 / 2 : ℝ) ^ 2 ≤ x ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hxhalf' 2
    have hy : 1 / 4 ≤ N * x ^ 2 := by nlinarith
    have hmain : 2 + u ≤ 16 * (N * x ^ 3 + N ^ 2 * x ^ 4) := by
      have hNx3 : 1 / 8 ≤ N * x ^ 3 := by nlinarith
      have hquad : N * x ^ 2 / 2 ≤ 16 * (N * x ^ 2) ^ 2 := by nlinarith
      dsimp [u]
      nlinarith [sq_nonneg (N * x ^ 2)]
    calc
      Real.exp (-N * x) * (2 + u) ≤
          Real.exp (-N * x) * (16 * (N * x ^ 3 + N ^ 2 * x ^ 4)) :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
      _ = 16 * Real.exp (-N * x) * (N * x ^ 3 + N ^ 2 * x ^ 4) := by ring

/-- Integrated second-order comparison between an endpoint moment kernel and its
Laplace kernel.  This form only needs local finiteness of the measure; the support
restriction is expressed by the set integral. -/
lemma abs_integral_one_sub_pow_sub_exp_quadratic_le
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (n : ℕ) (hn : 1 ≤ n) :
    |∫ x in Icc (0 : ℝ) 1,
        ((1 - x) ^ n - Real.exp (-(n : ℝ) * x) *
          (1 - (n : ℝ) * x ^ 2 / 2)) ∂μ| ≤
      ∫ x in Icc (0 : ℝ) 1,
        16 * Real.exp (-(n : ℝ) * x) *
          ((n : ℝ) * x ^ 3 + (n : ℝ) ^ 2 * x ^ 4) ∂μ := by
  have hg : IntegrableOn
      (fun x : ℝ ↦ 16 * Real.exp (-(n : ℝ) * x) *
        ((n : ℝ) * x ^ 3 + (n : ℝ) ^ 2 * x ^ 4)) (Icc 0 1) μ := by
    apply Continuous.integrableOn_Icc
    fun_prop
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hg
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs]
  exact abs_one_sub_pow_sub_exp_quadratic_le n hn hx.1 hx.2

/-- The integrated endpoint/Laplace comparison, expanded into raw Laplace moments. -/
lemma abs_endpointMoment_sub_laplace_secondOrder_le
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (n : ℕ) (hn : 1 ≤ n) :
    |(∫ x in Icc (0 : ℝ) 1, (1 - x) ^ n ∂μ) -
        ((∫ x in Icc (0 : ℝ) 1, Real.exp (-(n : ℝ) * x) ∂μ) -
          (n : ℝ) / 2 *
            ∫ x in Icc (0 : ℝ) 1,
              Real.exp (-(n : ℝ) * x) * x ^ 2 ∂μ)| ≤
      16 * ((n : ℝ) *
          ∫ x in Icc (0 : ℝ) 1,
            Real.exp (-(n : ℝ) * x) * x ^ 3 ∂μ +
        (n : ℝ) ^ 2 *
          ∫ x in Icc (0 : ℝ) 1,
            Real.exp (-(n : ℝ) * x) * x ^ 4 ∂μ) := by
  let N : ℝ := n
  let P : ℝ → ℝ := fun x ↦ (1 - x) ^ n
  let E : ℝ → ℝ := fun x ↦ Real.exp (-N * x)
  have hP : IntegrableOn P (Icc 0 1) μ := by
    apply Continuous.integrableOn_Icc
    dsimp [P]
    fun_prop
  have hE : IntegrableOn E (Icc 0 1) μ := by
    apply Continuous.integrableOn_Icc
    dsimp [E]
    fun_prop
  have hE2 : IntegrableOn (fun x ↦ E x * x ^ 2) (Icc 0 1) μ := by
    apply Continuous.integrableOn_Icc
    dsimp [E]
    fun_prop
  have hE3 : IntegrableOn (fun x ↦ E x * x ^ 3) (Icc 0 1) μ := by
    apply Continuous.integrableOn_Icc
    dsimp [E]
    fun_prop
  have hE4 : IntegrableOn (fun x ↦ E x * x ^ 4) (Icc 0 1) μ := by
    apply Continuous.integrableOn_Icc
    dsimp [E]
    fun_prop
  have hkernel :
      (∫ x in Icc (0 : ℝ) 1,
          (P x - E x * (1 - N * x ^ 2 / 2)) ∂μ) =
        (∫ x in Icc (0 : ℝ) 1, P x ∂μ) -
          ((∫ x in Icc (0 : ℝ) 1, E x ∂μ) -
            N / 2 * ∫ x in Icc (0 : ℝ) 1, E x * x ^ 2 ∂μ) := by
    calc
      (∫ x in Icc (0 : ℝ) 1,
          (P x - E x * (1 - N * x ^ 2 / 2)) ∂μ) =
          ∫ x in Icc (0 : ℝ) 1,
            (P x - (E x - (N / 2) * (E x * x ^ 2))) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (∫ x in Icc (0 : ℝ) 1, P x ∂μ) -
          ∫ x in Icc (0 : ℝ) 1,
            (E x - (N / 2) * (E x * x ^ 2)) ∂μ := by
            simpa only [Pi.sub_apply] using
              integral_sub hP (hE.sub (hE2.const_mul (N / 2)))
      _ = (∫ x in Icc (0 : ℝ) 1, P x ∂μ) -
          ((∫ x in Icc (0 : ℝ) 1, E x ∂μ) -
            N / 2 * ∫ x in Icc (0 : ℝ) 1, E x * x ^ 2 ∂μ) := by
            rw [integral_sub hE (hE2.const_mul _), integral_const_mul]
  have hbound :
      (∫ x in Icc (0 : ℝ) 1,
          16 * E x * (N * x ^ 3 + N ^ 2 * x ^ 4) ∂μ) =
        16 * (N * ∫ x in Icc (0 : ℝ) 1, E x * x ^ 3 ∂μ +
          N ^ 2 * ∫ x in Icc (0 : ℝ) 1, E x * x ^ 4 ∂μ) := by
    calc
      (∫ x in Icc (0 : ℝ) 1,
          16 * E x * (N * x ^ 3 + N ^ 2 * x ^ 4) ∂μ) =
          ∫ x in Icc (0 : ℝ) 1,
            ((16 * N) * (E x * x ^ 3) +
              (16 * N ^ 2) * (E x * x ^ 4)) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (16 * N) * ∫ x in Icc (0 : ℝ) 1, E x * x ^ 3 ∂μ +
          (16 * N ^ 2) * ∫ x in Icc (0 : ℝ) 1, E x * x ^ 4 ∂μ := by
            rw [integral_add (hE3.const_mul _) (hE4.const_mul _),
              integral_const_mul, integral_const_mul]
      _ = 16 * (N * ∫ x in Icc (0 : ℝ) 1, E x * x ^ 3 ∂μ +
          N ^ 2 * ∫ x in Icc (0 : ℝ) 1, E x * x ^ 4 ∂μ) := by ring
  have h := abs_integral_one_sub_pow_sub_exp_quadratic_le μ n hn
  dsimp [P, E, N] at hkernel hbound ⊢
  rw [← hkernel, ← hbound]
  exact h

/-- Raw-moment formulation of the endpoint/Laplace comparison. -/
lemma abs_unitEndpointMoment_sub_unitLaplace_secondOrder_le
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (n : ℕ) (hn : 1 ≤ n) :
    |unitEndpointMoment μ n -
        (unitLaplaceMoment μ n 0 -
          (n : ℝ) / 2 * unitLaplaceMoment μ n 2)| ≤
      16 * ((n : ℝ) * unitLaplaceMoment μ n 3 +
        (n : ℝ) ^ 2 * unitLaplaceMoment μ n 4) := by
  simpa [unitEndpointMoment, unitLaplaceMoment] using
    abs_endpointMoment_sub_laplace_secondOrder_le μ n hn

/-- Fully quantitative logarithmic endpoint/Laplace comparison.  The smallness
hypothesis is exactly what is needed to enter the radius `1 / 2` logarithm
chart; all other quantities are explicit tilted raw moments. -/
lemma abs_log_unitEndpointMoment_sub_log_unitLaplace_add_le
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (n : ℕ) (hn : 1 ≤ n)
    (hM : 0 < unitEndpointMoment μ n)
    (hB : 0 < unitLaplaceMoment μ n 0)
    (hsmall :
      |(n : ℝ) / 2 * unitLaplaceMoment μ n 2 /
          unitLaplaceMoment μ n 0| +
        16 * ((n : ℝ) * unitLaplaceMoment μ n 3 +
          (n : ℝ) ^ 2 * unitLaplaceMoment μ n 4) /
            unitLaplaceMoment μ n 0 ≤ 1 / 2) :
    |Real.log (unitEndpointMoment μ n) -
        Real.log (unitLaplaceMoment μ n 0) +
        (n : ℝ) / 2 * unitLaplaceMoment μ n 2 /
          unitLaplaceMoment μ n 0| ≤
      2 * ((n : ℝ) / 2 * unitLaplaceMoment μ n 2 /
          unitLaplaceMoment μ n 0) ^ 2 +
        2 * (16 * ((n : ℝ) * unitLaplaceMoment μ n 3 +
          (n : ℝ) ^ 2 * unitLaplaceMoment μ n 4) /
            unitLaplaceMoment μ n 0) := by
  let M := unitEndpointMoment μ n
  let B := unitLaplaceMoment μ n 0
  let a := (n : ℝ) / 2 * unitLaplaceMoment μ n 2 / B
  let ε := 16 * ((n : ℝ) * unitLaplaceMoment μ n 3 +
    (n : ℝ) ^ 2 * unitLaplaceMoment μ n 4) / B
  have hB0 : 0 ≤ B := hB.le
  have h3 : 0 ≤ unitLaplaceMoment μ n 3 := unitLaplaceMoment_nonneg _ _ _
  have h4 : 0 ≤ unitLaplaceMoment μ n 4 := unitLaplaceMoment_nonneg _ _ _
  have hε : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have happrox : |M / B - (1 - a)| ≤ ε := by
    have hraw := abs_unitEndpointMoment_sub_unitLaplace_secondOrder_le μ n hn
    have heq : M / B - (1 - a) =
        (M - (B - (n : ℝ) / 2 * unitLaplaceMoment μ n 2)) / B := by
      dsimp [M, B, a]
      field_simp [hB.ne']
    rw [heq, abs_div, abs_of_pos hB]
    exact (div_le_div_of_nonneg_right hraw hB0)
  simpa only [M, B, a, ε] using
    abs_log_sub_log_add_le_two_sq_add hM hB hε hsmall happrox

namespace ProbabilityRepresentation

lemma ae_weightedSumDistribution_mem_Icc :
    ∀ᵐ x ∂weightedSumDistribution, x ∈ Icc (0 : ℝ) 1 := by
  unfold weightedSumDistribution
  apply (ae_map_iff measurable_weightedCoordinateSum.aemeasurable
    (show MeasurableSet {x : ℝ | x ∈ Icc (0 : ℝ) 1} by
      exact measurableSet_Icc)).2
  filter_upwards with ω
  exact ⟨weightedCoordinateSum_nonneg ω, weightedCoordinateSum_le_one ω⟩

lemma weightedSumDistribution_restrict_Icc :
    weightedSumDistribution.restrict (Icc (0 : ℝ) 1) =
      weightedSumDistribution :=
  Measure.restrict_eq_self_of_ae_mem ae_weightedSumDistribution_mem_Icc

/-- The survival function of the weighted-sum law is Rvachev's bump on the
whole nonnegative ray, including beyond the compact support. -/
lemma weightedSumDistribution_real_Ioi_eq_rvachevUp_of_nonneg
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ} (ht : 0 ≤ t) :
    weightedSumDistribution.real (Ioi t) = rvachevUp F t := by
  calc
    weightedSumDistribution.real (Ioi t) =
        1 - weightedSumDistribution.real (Iic t) := by
      rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    _ = 1 - weightedSumCDF t := by
      rw [weightedSumCDF, ProbabilityTheory.cdf_eq_real]
    _ = 1 - fabiusReal F t := by
      rw [weightedSumCDF_eq_fabiusReal F hF t]
    _ = rvachevUp F t :=
      (rvachevUp_eq_one_sub_fabiusReal_of_nonneg F hF ht).symm

/-- Unit-interval compatibility form of
`weightedSumDistribution_real_Ioi_eq_rvachevUp_of_nonneg`. -/
lemma weightedSumDistribution_real_Ioi_eq_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    weightedSumDistribution.real (Ioi t) = rvachevUp F t :=
  weightedSumDistribution_real_Ioi_eq_rvachevUp_of_nonneg F hF ht.1

/-- Integration against the weighted-sum law in terms of the survival
function `rvachevUp`.  This is the compact-support expectation identity
`E[g(X)] = g(0) + ∫ g'(t) P(X > t) dt`. -/
theorem integral_unit_eq_zero_add_integral_deriv_mul_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F)
    (g g' : ℝ → ℝ) (hg : Continuous g) (hg' : Continuous g')
    (hderiv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' x) x) :
    (∫ x in Icc (0 : ℝ) 1, g x ∂weightedSumDistribution) =
      g 0 + ∫ t in (0 : ℝ)..1, g' t * rvachevUp F t := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let A : Set (ℝ × ℝ) := {z | z.1 < z.2}
  let H : ℝ × ℝ → ℝ := fun z => A.indicator (fun z => g' z.1) z
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_fst measurable_snd
  have hg'ν : Integrable g' ν := by
    dsimp [ν]
    exact hg'.integrableOn_Icc
  have hH : Integrable H (ν.prod weightedSumDistribution) := by
    have hbase : Integrable (fun z : ℝ × ℝ => g' z.1 * (1 : ℝ))
        (ν.prod weightedSumDistribution) :=
      hg'ν.mul_prod (integrable_const (1 : ℝ))
    have hi := hbase.indicator hA
    simpa only [H, one_mul, mul_one] using hi
  have hgμ : Integrable g weightedSumDistribution := by
    rw [← weightedSumDistribution_restrict_Icc]
    exact hg.integrableOn_Icc
  have hinner_t (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (∫ t : ℝ, H (t, x) ∂ν) = g x - g 0 := by
    have hind : (fun t : ℝ => H (t, x)) = (Iio x).indicator g' := by
      funext t
      simp only [H, A, Set.indicator, mem_setOf_eq, mem_Iio]
    rw [hind, integral_indicator measurableSet_Iio]
    change (∫ t : ℝ, g' t ∂(ν.restrict (Iio x))) = _
    rw [show ν.restrict (Iio x) = volume.restrict (Ico 0 x) by
      dsimp [ν]
      rw [Measure.restrict_restrict measurableSet_Iio]
      congr 1
      ext t
      simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor <;> intro ht
      · exact ⟨ht.2.1, ht.1⟩
      · exact ⟨ht.2, ht.1, (ht.2.trans_le hx.2).le⟩]
    rw [integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx.1]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      apply hderiv t
      rw [uIcc_of_le hx.1] at ht
      exact ⟨ht.1, ht.2.trans hx.2⟩
    · exact hg'.intervalIntegrable 0 x
  have hinner_x (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ x : ℝ, H (t, x) ∂weightedSumDistribution) =
        g' t * rvachevUp F t := by
    have hind : (fun x : ℝ => H (t, x)) =
        (Ioi t).indicator (fun _ => g' t) := by
      funext x
      simp only [H, A, Set.indicator, mem_setOf_eq, mem_Ioi]
    rw [hind, integral_indicator_const (g' t) measurableSet_Ioi]
    rw [weightedSumDistribution_real_Ioi_eq_rvachevUp F hF ht]
    simp only [smul_eq_mul]
    ring
  have horder_x :
      (∫ x : ℝ, ∫ t : ℝ, H (t, x) ∂ν ∂weightedSumDistribution) =
        (∫ x : ℝ, g x ∂weightedSumDistribution) - g 0 := by
    calc
      (∫ x : ℝ, ∫ t : ℝ, H (t, x) ∂ν ∂weightedSumDistribution) =
          ∫ x : ℝ, (g x - g 0) ∂weightedSumDistribution := by
            apply integral_congr_ae
            filter_upwards [ae_weightedSumDistribution_mem_Icc] with x hx
            exact hinner_t x hx
      _ = (∫ x : ℝ, g x ∂weightedSumDistribution) - g 0 := by
        rw [integral_sub hgμ (integrable_const _), integral_const,
          probReal_univ, one_smul]
  have horder_t :
      (∫ t : ℝ, ∫ x : ℝ, H (t, x) ∂weightedSumDistribution ∂ν) =
        ∫ t in (0 : ℝ)..1, g' t * rvachevUp F t := by
    calc
      (∫ t : ℝ, ∫ x : ℝ, H (t, x) ∂weightedSumDistribution ∂ν) =
          ∫ t in Icc (0 : ℝ) 1, g' t * rvachevUp F t := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            exact hinner_x t ht
      _ = ∫ t in (0 : ℝ)..1, g' t * rvachevUp F t := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          integral_Icc_eq_integral_Ioc]
  have hswap :
      (∫ x : ℝ, ∫ t : ℝ, H (t, x) ∂ν ∂weightedSumDistribution) =
        ∫ t : ℝ, ∫ x : ℝ, H (t, x) ∂weightedSumDistribution ∂ν := by
    exact (integral_prod_symm H hH).symm.trans (integral_prod H hH)
  rw [horder_x, horder_t] at hswap
  rw [show (∫ x in Icc (0 : ℝ) 1, g x ∂weightedSumDistribution) =
      ∫ x : ℝ, g x ∂weightedSumDistribution by
    rw [weightedSumDistribution_restrict_Icc]]
  linarith

/-- The raw Laplace moments of the weighted-sum probability law are the
survival-function moments from `LaplaceMoments`. -/
theorem unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    unitLaplaceMoment weightedSumDistribution s k =
      fabiusLaplaceMoment F k s := by
  cases k with
  | zero =>
      let g : ℝ → ℝ := fun x => Real.exp (-s * x)
      let g' : ℝ → ℝ := fun x =>
        Real.exp (-s * x) * (-s * 1)
      have hderiv (x : ℝ) : HasDerivAt g (g' x) x := by
        dsimp [g, g']
        simpa only [id_eq] using ((hasDerivAt_id x).const_mul (-s)).exp
      have h := integral_unit_eq_zero_add_integral_deriv_mul_rvachevUp
        F hF g g' (by fun_prop) (by fun_prop) (fun x _ => hderiv x)
      have htilt :
          (∫ t in (0 : ℝ)..1, g' t * rvachevUp F t) =
            -s * tiltedSurvivalMoment F 0 s := by
        unfold tiltedSurvivalMoment
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp [g']
        simp only [pow_zero, one_mul]
        ring
      rw [htilt] at h
      simpa [unitLaplaceMoment, g, fabiusLaplaceMoment,
        generatingFunction, tiltedSurvivalMoment] using h
  | succ k =>
      let g : ℝ → ℝ :=
        (fun x => Real.exp (-s * x)) * fun x => x ^ (k + 1)
      let g' : ℝ → ℝ := fun x =>
        Real.exp (-s * x) * (-s * 1) * x ^ (k + 1) +
          Real.exp (-s * x) *
            (((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1))
      have hderiv (x : ℝ) : HasDerivAt g (g' x) x := by
        dsimp [g, g']
        simpa only [id_eq, Nat.add_sub_cancel] using
          ((hasDerivAt_id x).const_mul (-s)).exp.mul
            (hasDerivAt_pow (k + 1) x)
      have h := integral_unit_eq_zero_add_integral_deriv_mul_rvachevUp
        F hF g g' (by fun_prop) (by fun_prop) (fun x _ => hderiv x)
      have hIk : IntervalIntegrable
          (fun t : ℝ => t ^ k * rvachevUp F t * Real.exp (-s * t))
          volume 0 1 := by
        apply Continuous.intervalIntegrable
        exact ((continuous_id.pow k).mul
          (rvachev_contDiff F hF).continuous).mul (by fun_prop)
      have hIk1 : IntervalIntegrable
          (fun t : ℝ => t ^ (k + 1) * rvachevUp F t * Real.exp (-s * t))
          volume 0 1 := by
        apply Continuous.intervalIntegrable
        exact ((continuous_id.pow (k + 1)).mul
          (rvachev_contDiff F hF).continuous).mul (by fun_prop)
      have htilt :
          (∫ t in (0 : ℝ)..1, g' t * rvachevUp F t) =
            (k + 1 : ℝ) * tiltedSurvivalMoment F k s -
              s * tiltedSurvivalMoment F (k + 1) s := by
        calc
          (∫ t in (0 : ℝ)..1, g' t * rvachevUp F t) =
              ∫ t in (0 : ℝ)..1,
                ((k + 1 : ℝ) *
                    (t ^ k * rvachevUp F t * Real.exp (-s * t)) -
                  s * (t ^ (k + 1) * rvachevUp F t *
                    Real.exp (-s * t))) := by
                apply intervalIntegral.integral_congr
                intro t _ht
                dsimp [g']
                push_cast
                ring
          _ = (k + 1 : ℝ) *
                (∫ t in (0 : ℝ)..1,
                  t ^ k * rvachevUp F t * Real.exp (-s * t)) -
              s * (∫ t in (0 : ℝ)..1,
                t ^ (k + 1) * rvachevUp F t * Real.exp (-s * t)) := by
                rw [intervalIntegral.integral_sub
                  (hIk.const_mul _) (hIk1.const_mul _),
                  intervalIntegral.integral_const_mul,
                  intervalIntegral.integral_const_mul]
          _ = (k + 1 : ℝ) * tiltedSurvivalMoment F k s -
              s * tiltedSurvivalMoment F (k + 1) s := by
                rfl
      rw [htilt] at h
      simpa [unitLaplaceMoment, g, fabiusLaplaceMoment] using h

/-- Reflection invariance identifies the endpoint power moment with the
ordinary raw moment, represented here as the zero-tilt Laplace moment. -/
theorem unitEndpointMoment_weightedSumDistribution_eq_unitLaplaceMoment_zero
    (n : ℕ) :
    unitEndpointMoment weightedSumDistribution n =
      unitLaplaceMoment weightedSumDistribution 0 n := by
  let r : ℝ → ℝ := fun x => 1 - x
  have hr : Measurable r := by
    dsimp [r]
    fun_prop
  have hmap :
      (∫ y : ℝ, y ^ n ∂weightedSumDistribution.map r) =
        ∫ x : ℝ, (1 - x) ^ n ∂weightedSumDistribution := by
    simpa only [r, Pi.pow_apply, id_eq] using integral_map hr.aemeasurable
      (continuous_id.pow n).aestronglyMeasurable
  have hreflect :
      (∫ x : ℝ, (1 - x) ^ n ∂weightedSumDistribution) =
        ∫ x : ℝ, x ^ n ∂weightedSumDistribution := by
    rw [← hmap, weightedSumDistribution_reflection]
  calc
    unitEndpointMoment weightedSumDistribution n =
        ∫ x : ℝ, (1 - x) ^ n ∂weightedSumDistribution := by
      unfold unitEndpointMoment
      rw [weightedSumDistribution_restrict_Icc]
    _ = ∫ x : ℝ, x ^ n ∂weightedSumDistribution := hreflect
    _ = unitLaplaceMoment weightedSumDistribution 0 n := by
      unfold unitLaplaceMoment
      rw [weightedSumDistribution_restrict_Icc]
      simp

/-- The zero-tilt zeroth moment has total mass one. -/
@[simp] theorem unitLaplaceMoment_weightedSumDistribution_zero_zero :
    unitLaplaceMoment weightedSumDistribution 0 0 = 1 := by
  unfold unitLaplaceMoment
  rw [weightedSumDistribution_restrict_Icc]
  simp

/-- Exact endpoint-moment normalization in degree zero. -/
@[simp] theorem unitEndpointMoment_weightedSumDistribution_zero :
    unitEndpointMoment weightedSumDistribution 0 = 1 := by
  rw [unitEndpointMoment_weightedSumDistribution_eq_unitLaplaceMoment_zero,
    unitLaplaceMoment_weightedSumDistribution_zero_zero]

/-- At zero tilt, the raw moments of the weighted-sum law are exactly the
rational half moments. -/
theorem unitLaplaceMoment_weightedSumDistribution_zero_eq_halfMoment
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    unitLaplaceMoment weightedSumDistribution 0 n = (halfMoment n : ℝ) := by
  calc
    unitLaplaceMoment weightedSumDistribution 0 n =
        fabiusLaplaceMoment F n 0 :=
      unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
        F hF n 0
    _ = (halfMoment n : ℝ) :=
      fabiusLaplaceMoment_zero_eq_halfMoment F hF n

/-- Reflection invariance identifies the endpoint power moment with the
ordinary power moment, hence with `halfMoment`. -/
theorem unitEndpointMoment_weightedSumDistribution_eq_halfMoment
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    unitEndpointMoment weightedSumDistribution n = (halfMoment n : ℝ) := by
  calc
    unitEndpointMoment weightedSumDistribution n =
        unitLaplaceMoment weightedSumDistribution 0 n :=
      unitEndpointMoment_weightedSumDistribution_eq_unitLaplaceMoment_zero n
    _ = (halfMoment n : ℝ) :=
      unitLaplaceMoment_weightedSumDistribution_zero_eq_halfMoment F hF n

end ProbabilityRepresentation

lemma fabiusLaplaceMoment_nonneg
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    0 ≤ fabiusLaplaceMoment F k s := by
  rw [← ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
    F hF k s]
  exact unitLaplaceMoment_nonneg _ _ _

/-- Endpoint/Laplace comparison expressed entirely through the canonical
Fabius half moment and tilted moments. -/
theorem abs_halfMoment_sub_fabiusLaplace_secondOrder_le
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    |(halfMoment n : ℝ) -
        (fabiusLaplaceMoment F 0 n -
          (n : ℝ) / 2 * fabiusLaplaceMoment F 2 n)| ≤
      16 * ((n : ℝ) * fabiusLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * fabiusLaplaceMoment F 4 n) := by
  have h := abs_unitEndpointMoment_sub_unitLaplace_secondOrder_le
    ProbabilityRepresentation.weightedSumDistribution n hn
  rw [ProbabilityRepresentation.unitEndpointMoment_weightedSumDistribution_eq_halfMoment
      F hF n] at h
  simpa only [ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
    F hF] using h

/-- Relative endpoint/Laplace comparison. -/
theorem abs_halfMoment_div_fabiusLaplace_sub_secondOrder_le
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    |(halfMoment n : ℝ) / fabiusLaplaceMoment F 0 n -
        (1 - (n : ℝ) / 2 * normalizedLaplaceMoment F 2 n)| ≤
      16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hB := fabiusLaplaceMoment_zero_pos F hF hn0
  have hraw := abs_halfMoment_sub_fabiusLaplace_secondOrder_le F hF n hn
  unfold normalizedLaplaceMoment
  have heq :
      (halfMoment n : ℝ) / fabiusLaplaceMoment F 0 n -
          (1 - (n : ℝ) / 2 *
            (fabiusLaplaceMoment F 2 n / fabiusLaplaceMoment F 0 n)) =
        ((halfMoment n : ℝ) -
          (fabiusLaplaceMoment F 0 n -
            (n : ℝ) / 2 * fabiusLaplaceMoment F 2 n)) /
              fabiusLaplaceMoment F 0 n := by
    field_simp [hB.ne']
  rw [heq, abs_div, abs_of_pos hB]
  calc
    |(halfMoment n : ℝ) -
          (fabiusLaplaceMoment F 0 n -
            (n : ℝ) / 2 * fabiusLaplaceMoment F 2 n)| /
        fabiusLaplaceMoment F 0 n ≤
        (16 * ((n : ℝ) * fabiusLaplaceMoment F 3 n +
          (n : ℝ) ^ 2 * fabiusLaplaceMoment F 4 n)) /
            fabiusLaplaceMoment F 0 n :=
      div_le_div_of_nonneg_right hraw hB.le
    _ = 16 * ((n : ℝ) *
          (fabiusLaplaceMoment F 3 n / fabiusLaplaceMoment F 0 n) +
        (n : ℝ) ^ 2 *
          (fabiusLaplaceMoment F 4 n / fabiusLaplaceMoment F 0 n)) := by
      field_simp [hB.ne']

/-- The raw second tilted moment is `q'' + (q')²`, where
`q = negativeLaplaceLog`. -/
lemma normalizedLaplaceMoment_two_eq_logSecond_add_first_sq
    (F : BoundedFabius) (s : ℝ) :
    normalizedLaplaceMoment F 2 s =
      negativeLaplaceLogSecond F s + negativeLaplaceLogFirst F s ^ 2 := by
  unfold negativeLaplaceLogSecond negativeLaplaceLogFirst
  ring

/-- Explicit second-order expansion of the dyadic endpoint/Laplace logarithm.
The right side is quantitative; the sole local hypothesis says the displayed
relative correction lies in the radius-`1/2` logarithm chart. -/
theorem abs_dyadicEndpointLaplaceLogError_add_secondOrder_le
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n)
    (hsmall :
      |(n : ℝ) / 2 *
          (negativeLaplaceLogSecond F n +
            negativeLaplaceLogFirst F n ^ 2)| +
        16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
          (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) ≤ 1 / 2) :
    |dyadicEndpointLaplaceLogError n +
        (n : ℝ) / 2 *
          (negativeLaplaceLogSecond F n +
            negativeLaplaceLogFirst F n ^ 2)| ≤
      2 * ((n : ℝ) / 2 *
          (negativeLaplaceLogSecond F n +
            negativeLaplaceLogFirst F n ^ 2)) ^ 2 +
        2 * (16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
          (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : 0 < (halfMoment n : ℝ) := by
    exact_mod_cast halfMoment_pos n
  have hB := fabiusLaplaceMoment_zero_pos F hF hn0
  let a : ℝ := (n : ℝ) / 2 * normalizedLaplaceMoment F 2 n
  let ε : ℝ := 16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
    (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)
  have h3 : 0 ≤ normalizedLaplaceMoment F 3 n := by
    unfold normalizedLaplaceMoment
    exact div_nonneg (fabiusLaplaceMoment_nonneg F hF 3 n) hB.le
  have h4 : 0 ≤ normalizedLaplaceMoment F 4 n := by
    unfold normalizedLaplaceMoment
    exact div_nonneg (fabiusLaplaceMoment_nonneg F hF 4 n) hB.le
  have hε : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have happrox :
      |(halfMoment n : ℝ) / fabiusLaplaceMoment F 0 n - (1 - a)| ≤ ε := by
    exact abs_halfMoment_div_fabiusLaplace_sub_secondOrder_le F hF n hn
  have ha : a = (n : ℝ) / 2 *
      (negativeLaplaceLogSecond F n + negativeLaplaceLogFirst F n ^ 2) := by
    dsimp [a]
    rw [normalizedLaplaceMoment_two_eq_logSecond_add_first_sq]
  have hsmall' : |a| + ε ≤ 1 / 2 := by
    rw [ha]
    exact hsmall
  have hlog := abs_log_sub_log_add_le_two_sq_add hm hB hε hsmall' happrox
  rw [← negativeLaplaceLog_eq_log_laplaceMoment F hF hn0] at hlog
  rw [ha] at hlog
  simpa only [dyadicEndpointLaplaceLogError, ε] using hlog

/-- Conditional sharp `O(1/n)` endpoint expansion.  Its two hypotheses are
exactly the quantitative derivative/moment estimates left to the periodic
analysis: the square of the second-order term and the normalized third/fourth
moment remainder are both `O(1/n)`. -/
theorem dyadicEndpointLaplaceLogError_add_secondOrder_isBigO
    (F : BoundedFabius) (hF : IsFabius F)
    (hsecond :
      (fun n : ℕ => ((n : ℝ) / 2 *
        (negativeLaplaceLogSecond F n +
          negativeLaplaceLogFirst F n ^ 2)) ^ 2) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹))
    (hhigher :
      (fun n : ℕ => 16 *
        ((n : ℝ) * normalizedLaplaceMoment F 3 n +
          (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹)) :
    (fun n : ℕ => dyadicEndpointLaplaceLogError n +
      (n : ℝ) / 2 *
        (negativeLaplaceLogSecond F n +
          negativeLaplaceLogFirst F n ^ 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  let m : ℕ → ℝ := fun n => (halfMoment n : ℝ)
  let b : ℕ → ℝ := fun n => fabiusLaplaceMoment F 0 n
  let a : ℕ → ℝ := fun n => (n : ℝ) / 2 *
    (negativeLaplaceLogSecond F n + negativeLaplaceLogFirst F n ^ 2)
  let ε : ℕ → ℝ := fun n => 16 *
    ((n : ℝ) * normalizedLaplaceMoment F 3 n +
      (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)
  let invN : ℕ → ℝ := fun n => (n : ℝ)⁻¹
  have hn_event : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
    eventually_atTop.2 ⟨1, fun _ hn => hn⟩
  have hm : ∀ᶠ n in atTop, 0 < m n := by
    filter_upwards with n
    dsimp [m]
    exact_mod_cast halfMoment_pos n
  have hb : ∀ᶠ n in atTop, 0 < b n := by
    filter_upwards [hn_event] with n hn
    dsimp [b]
    apply fabiusLaplaceMoment_zero_pos F hF
    exact_mod_cast (show 0 < n by omega)
  have hε0 : ∀ᶠ n in atTop, 0 ≤ ε n := by
    filter_upwards [hn_event] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hB := fabiusLaplaceMoment_zero_pos F hF hn0
    have h3 : 0 ≤ normalizedLaplaceMoment F 3 n := by
      unfold normalizedLaplaceMoment
      exact div_nonneg (fabiusLaplaceMoment_nonneg F hF 3 n) hB.le
    have h4 : 0 ≤ normalizedLaplaceMoment F 4 n := by
      unfold normalizedLaplaceMoment
      exact div_nonneg (fabiusLaplaceMoment_nonneg F hF 4 n) hB.le
    dsimp [ε]
    positivity
  have happrox : ∀ᶠ n in atTop,
      |m n / b n - (1 - a n)| ≤ ε n := by
    filter_upwards [hn_event] with n hn
    have hraw :=
      abs_halfMoment_div_fabiusLaplace_sub_secondOrder_le F hF n hn
    have ha : a n =
        (n : ℝ) / 2 * normalizedLaplaceMoment F 2 n := by
      dsimp [a]
      rw [normalizedLaplaceMoment_two_eq_logSecond_add_first_sq]
    rw [ha]
    exact hraw
  have ha_sq : (fun n => (a n) ^ 2) =O[atTop] invN := by
    simpa only [a, invN] using hsecond
  have hε : ε =O[atTop] invN := by
    simpa only [ε, invN] using hhigher
  have hinv : Tendsto invN atTop (𝓝 0) := by
    dsimp [invN]
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ha_sq_zero : Tendsto (fun n => (a n) ^ 2) atTop (𝓝 0) :=
    ha_sq.trans_tendsto hinv
  have habs_zero : Tendsto (fun n => |a n|) atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp ha_sq_zero
    change Tendsto (fun n => Real.sqrt ((a n) ^ 2)) atTop
      (𝓝 (Real.sqrt 0)) at hsqrt
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsqrt
  have hε_zero : Tendsto ε atTop (𝓝 0) := hε.trans_tendsto hinv
  have hsmall : ∀ᶠ n in atTop, |a n| + ε n ≤ 1 / 2 := by
    have hsum : Tendsto (fun n => |a n| + ε n) atTop (𝓝 0) := by
      simpa only [zero_add] using habs_zero.add hε_zero
    exact ((tendsto_order.1 hsum).2 (1 / 2) (by norm_num)).mono
      fun _ h => h.le
  have hlog := log_secondOrder_transfer_isBigO atTop m b a ε invN
    hm hb hε0 hsmall happrox ha_sq hε
  apply hlog.congr'
  · filter_upwards [hn_event] with n hn
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    dsimp [m, b, a]
    unfold dyadicEndpointLaplaceLogError
    rw [negativeLaplaceLog_eq_log_laplaceMoment F hF hn0]
    rfl
  · exact Filter.EventuallyEq.rfl

end Fabius
