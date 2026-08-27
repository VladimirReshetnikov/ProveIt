import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Shell linearity forced by an unrestricted Cesàro limit

The first step of Document 7's obstruction theorems (audited in the
second-wave comparative audit): if a cumulative mass function
satisfies the unrestricted Cesàro normalization `F(t)/(t-t₀) → 1`,
then its normalized increments over partial dyadic shells converge to
the *linear* profile,

`(F(2ᵏ(1+z)) - F(2ᵏ))/2ᵏ → z`.

Applied with `F(t) = ∫_{t₀}^t |f|/g`, this says that a gauge attaining
the exact Cesàro limit forces the within-shell mass of `|f|/g` to
distribute like Lebesgue measure — which the singular limiting shell
measure of the natural gauge forbids for every stabilizing or
bounded-distortion gauge, and which the shell-adaptive gauge of
Documents 7/8 achieves by ever finer equalization.  This module
formalizes the purely limit-theoretic step; the statement is for an
arbitrary function `F`, so it applies verbatim to any future
formalization of the mass integrals.

* `tendsto_ray_div_two_pow` — along any geometric ray `2ᵏc` (`c > 0`),
  the normalization transports: `F(2ᵏc)/2ᵏ → c`.
* `tendsto_shell_increment` — the shell-linearity lemma.
-/

set_option autoImplicit false

open Filter

namespace Fabius

/-- If `F(t)/(t - t₀) → 1` as `t → ∞`, then along any geometric ray
`2ᵏ·c` with `c > 0`, `F(2ᵏc)/2ᵏ → c`. -/
theorem tendsto_ray_div_two_pow {F : ℝ → ℝ} {t₀ : ℝ}
    (hF : Tendsto (fun t => F t / (t - t₀)) atTop (nhds 1))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => F ((2:ℝ) ^ k * c) / 2 ^ k) atTop (nhds c) := by
  have hpow : Tendsto (fun k : ℕ => (2:ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hxk : Tendsto (fun k : ℕ => (2:ℝ) ^ k * c) atTop atTop :=
    hpow.atTop_mul_const hc
  have h1 : Tendsto (fun k : ℕ =>
      F ((2:ℝ) ^ k * c) / ((2:ℝ) ^ k * c - t₀)) atTop (nhds 1) := hF.comp hxk
  have h2 : Tendsto (fun k : ℕ => ((2:ℝ) ^ k * c - t₀) / 2 ^ k)
      atTop (nhds c) := by
    have h3 : Tendsto (fun k : ℕ => t₀ * ((1:ℝ) / 2) ^ k) atTop (nhds 0) := by
      have h4 := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      simpa using h4.const_mul t₀
    have h5 : Tendsto (fun k : ℕ => c - t₀ * ((1:ℝ) / 2) ^ k)
        atTop (nhds (c - 0)) := tendsto_const_nhds.sub h3
    rw [sub_zero] at h5
    refine h5.congr fun k => ?_
    have hp : ((2:ℝ) ^ k) ≠ 0 := by positivity
    have hcancel : ((1:ℝ) / 2) ^ k * 2 ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    rw [eq_div_iff hp, sub_mul, mul_assoc, hcancel, mul_one]
    ring
  have hmul := h1.mul h2
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [hxk.eventually_gt_atTop t₀] with k hk
  have hne : ((2:ℝ) ^ k * c - t₀) ≠ 0 := by linarith
  have hp : ((2:ℝ) ^ k) ≠ 0 := by positivity
  field_simp

/-- **Shell linearity** (Document 7, first lemma of the obstruction
theorems): an unrestricted Cesàro normalization
`F(t)/(t-t₀) → 1` forces the normalized partial-shell increments to be
asymptotically linear, `(F(2ᵏ(1+z)) - F(2ᵏ))/2ᵏ → z` for every
`z ≥ 0`.  In the audit this is what makes the within-shell mass of an
exact gauge converge weakly to Lebesgue measure. -/
theorem tendsto_shell_increment {F : ℝ → ℝ} {t₀ : ℝ}
    (hF : Tendsto (fun t => F t / (t - t₀)) atTop (nhds 1)) {z : ℝ}
    (hz : 0 ≤ z) :
    Tendsto (fun k : ℕ =>
        (F ((2:ℝ) ^ k * (1 + z)) - F (2 ^ k)) / 2 ^ k)
      atTop (nhds z) := by
  have h1 := tendsto_ray_div_two_pow hF (by linarith : (0:ℝ) < 1 + z)
  have h2 := tendsto_ray_div_two_pow hF (by norm_num : (0:ℝ) < 1)
  have h3 := h1.sub h2
  rw [show (1 + z) - 1 = z by ring] at h3
  refine h3.congr fun k => ?_
  rw [mul_one, sub_div]

end Fabius
