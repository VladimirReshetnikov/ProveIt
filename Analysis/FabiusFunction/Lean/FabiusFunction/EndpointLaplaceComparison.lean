import FabiusFunction.DyadicSharpDecomposition
import FabiusFunction.ProbabilityLaplaceMoments
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Endpoint moments versus the negative Laplace transform

This module supplies the real-variable comparison needed to pass from the
Fabius endpoint moment `halfMoment n` to the negative Laplace transform at
scale `n`.

Its main ingredients are:

* a pointwise second-order comparison of `(1 - x)^n` with
  `exp (-n*x) * (1 - n*x^2/2)` on `[0,1]`;
* the imported Fubini/CDF bridge from `ProbabilityLaplaceMoments`, identifying
  integrals against the weighted-sum law with survival-function moments;
* a quantitative local logarithm lemma; and
* an `O(1/n)` transfer theorem whose remaining hypotheses are precisely the
  normalized tilted third/fourth-moment estimates supplied by the sharp
  periodic/saddle analysis.

The explicit logarithmic correction is

`n/2 * (negativeLaplaceLogSecond F n + negativeLaplaceLogFirst F n ^ 2)`,

which is `n/2` times the normalized second tilted moment.

Each finite comparison is also exposed by a zero-inclusive `_all` theorem;
the original positive-index names remain compatibility interfaces.

The imported probability bridge also records the survival identity on the full
nonnegative ray and separates reflection invariance from the zero-tilt and
degree-zero moment normalizations.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Fabius

/-- On `[0, 1/2]`, the quadratic Taylor truncation of `log (1 - x)` has
absolute remainder at most `2 * x^3 / 3`. -/
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

/-- For nonnegative `u`, `exp (-u)` differs from its linear truncation
`1 - u` by at most `u^2`. -/
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

/-- The real exponential is `1`-Lipschitz between two nonpositive exponents. -/
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
    ring_nf
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

/-- Zero-inclusive pointwise endpoint/Laplace comparison.  At `n = 0` both
sides vanish; positive indices are covered by
`abs_one_sub_pow_sub_exp_quadratic_le`. -/
lemma abs_one_sub_pow_sub_exp_quadratic_le_all
    (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(1 - x) ^ n - Real.exp (-(n : ℝ) * x) *
        (1 - (n : ℝ) * x ^ 2 / 2)| ≤
      16 * Real.exp (-(n : ℝ) * x) *
        ((n : ℝ) * x ^ 3 + (n : ℝ) ^ 2 * x ^ 4) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · exact abs_one_sub_pow_sub_exp_quadratic_le n (by omega) hx0 hx1

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

/-- Zero-inclusive integrated endpoint/Laplace comparison.  At `n = 0` both
integrands vanish, while positive indices are covered by
`abs_integral_one_sub_pow_sub_exp_quadratic_le`. -/
lemma abs_integral_one_sub_pow_sub_exp_quadratic_le_all
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (n : ℕ) :
    |∫ x in Icc (0 : ℝ) 1,
        ((1 - x) ^ n - Real.exp (-(n : ℝ) * x) *
          (1 - (n : ℝ) * x ^ 2 / 2)) ∂μ| ≤
      ∫ x in Icc (0 : ℝ) 1,
        16 * Real.exp (-(n : ℝ) * x) *
          ((n : ℝ) * x ^ 3 + (n : ℝ) ^ 2 * x ^ 4) ∂μ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact abs_integral_one_sub_pow_sub_exp_quadratic_le μ n (by omega)

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

/-- Zero-inclusive raw integral form of the endpoint/Laplace comparison.  The
boundary case `n = 0` is an exact identity, and positive indices are covered by
`abs_endpointMoment_sub_laplace_secondOrder_le`. -/
lemma abs_endpointMoment_sub_laplace_secondOrder_le_all
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (n : ℕ) :
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
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact abs_endpointMoment_sub_laplace_secondOrder_le μ n (by omega)

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

/-- Zero-inclusive raw-moment formulation of the endpoint/Laplace comparison.
At degree zero the endpoint and Laplace kernels coincide and the displayed
remainder vanishes. -/
lemma abs_unitEndpointMoment_sub_unitLaplace_secondOrder_le_all
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (n : ℕ) :
    |unitEndpointMoment μ n -
        (unitLaplaceMoment μ n 0 -
          (n : ℝ) / 2 * unitLaplaceMoment μ n 2)| ≤
      16 * ((n : ℝ) * unitLaplaceMoment μ n 3 +
        (n : ℝ) ^ 2 * unitLaplaceMoment μ n 4) := by
  simpa [unitEndpointMoment, unitLaplaceMoment] using
    abs_endpointMoment_sub_laplace_secondOrder_le_all μ n

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

/-- Zero-inclusive quantitative logarithmic endpoint/Laplace comparison.  The
explicit positivity and logarithm-chart hypotheses suffice at every natural
index, including the exact boundary identity at `n = 0`. -/
lemma abs_log_unitEndpointMoment_sub_log_unitLaplace_add_le_all
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (n : ℕ)
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
    have hraw := abs_unitEndpointMoment_sub_unitLaplace_secondOrder_le_all μ n
    have heq : M / B - (1 - a) =
        (M - (B - (n : ℝ) / 2 * unitLaplaceMoment μ n 2)) / B := by
      dsimp [M, B, a]
      field_simp [hB.ne']
    rw [heq, abs_div, abs_of_pos hB]
    exact (div_le_div_of_nonneg_right hraw hB0)
  simpa only [M, B, a, ε] using
    abs_log_sub_log_add_le_two_sq_add hM hB hε hsmall happrox


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

/-- Zero-inclusive endpoint/Laplace comparison for the canonical Fabius half
moment.  The probability-law bridge identifies the exact boundary case as
well as every positive index. -/
theorem abs_halfMoment_sub_fabiusLaplace_secondOrder_le_all
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) :
    |(halfMoment n : ℝ) -
        (fabiusLaplaceMoment F 0 n -
          (n : ℝ) / 2 * fabiusLaplaceMoment F 2 n)| ≤
      16 * ((n : ℝ) * fabiusLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * fabiusLaplaceMoment F 4 n) := by
  have h := abs_unitEndpointMoment_sub_unitLaplace_secondOrder_le_all
    ProbabilityRepresentation.weightedSumDistribution n
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

/-- Zero-inclusive relative endpoint/Laplace comparison.  The zeroth Laplace
moment is globally positive, so normalization remains valid at `n = 0`, where
both sides vanish. -/
theorem abs_halfMoment_div_fabiusLaplace_sub_secondOrder_le_all
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) :
    |(halfMoment n : ℝ) / fabiusLaplaceMoment F 0 n -
        (1 - (n : ℝ) / 2 * normalizedLaplaceMoment F 2 n)| ≤
      16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) := by
  have hB := fabiusLaplaceMoment_zero_pos_all F hF n
  have hraw := abs_halfMoment_sub_fabiusLaplace_secondOrder_le_all F hF n
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

/-- Zero-inclusive finite dyadic endpoint/Laplace logarithm estimate.  At
`n = 0` the endpoint error and every displayed correction vanish exactly;
positive indices are covered by
`abs_dyadicEndpointLaplaceLogError_add_secondOrder_le`. -/
theorem abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_all
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ)
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
  cases n with
  | zero =>
      have hlog0 : negativeLaplaceLog 0 = 0 := by
        simp [negativeLaplaceLog, negativeLaplaceTerm, negativeLaplaceKernel]
      simp [dyadicEndpointLaplaceLogError, halfMoment_zero, hlog0]
  | succ n =>
      exact abs_dyadicEndpointLaplaceLogError_add_secondOrder_le
        F hF (n + 1) (by omega) hsmall

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
