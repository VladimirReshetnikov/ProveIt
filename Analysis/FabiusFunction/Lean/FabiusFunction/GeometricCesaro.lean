import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Weighted Cesàro convergence and the geometric-shell average

The summation backbone of the Fourier-decay audit's mean theorems.
Every shell-sum argument there has the shape: the per-shell means
`β k` converge, the shell weights are `2ᵏ`, hence the aggregated
average converges to the same limit — with the last (largest) shell
carrying a fixed positive fraction of the total weight, this is *not*
the classical equal-weight Cesàro theorem, but its weighted Toeplitz
form.

* `tendsto_weighted_average` — the **general weighted Cesàro
  theorem**: for nonnegative weights `w` with divergent partial sums,
  `β k → L` implies `(∑_{j<K} w j·β j)/(∑_{j<K} w j) → L`.  Proved by
  Mathlib's `Asymptotics.IsLittleO.sum_range` applied to
  `w·(β - L) =o[atTop] w`.
* `tendsto_geom_shell_average` — the audit's geometric case:
  `β k → L` implies `(∑_{j<K} 2ʲ·β j)/2ᴷ → L`.  This is the exact
  step that aggregates full dyadic shells in the proofs of the
  Cesàro-profile and logarithmic-mean theorems (`∑_{j<K} 2ʲ(1+o(1))
  = 2ᴷ(1+o(1))`).
-/

set_option autoImplicit false

open Finset Filter Asymptotics

namespace Fabius

/-- **Weighted Cesàro convergence** (Toeplitz): if the weights `w` are
nonnegative with divergent partial sums and `β → L`, then the
`w`-weighted averages of `β` converge to `L`. -/
theorem tendsto_weighted_average {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hdiv : Tendsto (fun K => ∑ j ∈ range K, w j) atTop atTop)
    {β : ℕ → ℝ} {L : ℝ} (hβ : Tendsto β atTop (nhds L)) :
    Tendsto (fun K => (∑ j ∈ range K, w j * β j) / ∑ j ∈ range K, w j)
      atTop (nhds L) := by
  have h1 : (fun j => β j - L) =o[atTop] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr hβ)
  have hfo : (fun j => w j * (β j - L)) =o[atTop] w := by
    have h2 := h1.mul_isBigO (isBigO_refl w atTop)
    have h3 : (fun j => (β j - L) * w j) = fun j => w j * (β j - L) := by
      funext j
      ring
    simpa [h3] using h2
  have hsum := hfo.sum_range hw hdiv
  have hratio : Tendsto
      (fun K => (∑ j ∈ range K, w j * (β j - L)) / ∑ j ∈ range K, w j)
      atTop (nhds 0) := hsum.tendsto_div_nhds_zero
  have heq : ∀ᶠ K in atTop,
      (∑ j ∈ range K, w j * (β j - L)) / (∑ j ∈ range K, w j) + L =
        (∑ j ∈ range K, w j * β j) / ∑ j ∈ range K, w j := by
    filter_upwards [hdiv.eventually_gt_atTop 0] with K hK
    have hne : (∑ j ∈ range K, w j) ≠ 0 := ne_of_gt hK
    have hsplit : ∑ j ∈ range K, w j * (β j - L) =
        (∑ j ∈ range K, w j * β j) - L * ∑ j ∈ range K, w j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, sub_div, mul_div_assoc, div_self hne, mul_one, sub_add_cancel]
  have hlim : Tendsto
      (fun K => (∑ j ∈ range K, w j * (β j - L)) /
        (∑ j ∈ range K, w j) + L) atTop (nhds L) := by
    simpa using hratio.add_const L
  exact hlim.congr' heq

/-- **The geometric shell average of the decay audit**: if the
per-shell means `β k` converge to `L`, then
`(∑_{j<K} 2ʲ β j)/2ᴷ → L` — completed dyadic shells aggregate to the
same limit even though the last shell carries half the total weight. -/
theorem tendsto_geom_shell_average {β : ℕ → ℝ} {L : ℝ}
    (hβ : Tendsto β atTop (nhds L)) :
    Tendsto (fun K => (∑ j ∈ range K, 2 ^ j * β j) / 2 ^ K)
      atTop (nhds L) := by
  have hgeom : ∀ K : ℕ, ∑ j ∈ range K, (2:ℝ) ^ j = 2 ^ K - 1 := by
    intro K
    rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1) K]
    norm_num
  have hdiv : Tendsto (fun K => ∑ j ∈ range K, (2:ℝ) ^ j) atTop atTop := by
    simp only [hgeom]
    exact tendsto_atTop_add_const_right _ (-1)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)) |>.congr
      fun K => by ring
  have h1 := tendsto_weighted_average (w := fun j => (2:ℝ) ^ j)
    (fun j => by positivity) hdiv hβ
  have h2 : Tendsto (fun K : ℕ => ((2:ℝ) ^ K - 1) / 2 ^ K) atTop (nhds 1) := by
    have h3 : Tendsto (fun K : ℕ => 1 - ((1:ℝ) / 2) ^ K) atTop (nhds 1) := by
      have h4 := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1/2 : ℝ) < 1)
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub h4
    refine h3.congr fun K => ?_
    have hpow : (0:ℝ) < 2 ^ K := by positivity
    have hcancel : ((1:ℝ) / 2) ^ K * 2 ^ K = 1 := by
      rw [← mul_pow]
      norm_num
    rw [eq_div_iff (ne_of_gt hpow), sub_mul, one_mul, hcancel]
  have hmul := h1.mul h2
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with K hK
  have hne : ((2:ℝ) ^ K - 1) ≠ 0 := by
    have h5 : (2:ℝ) ≤ 2 ^ K := by
      calc (2:ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK
    intro h0
    nlinarith
  have hpow : ((2:ℝ) ^ K) ≠ 0 := by positivity
  rw [hgeom]
  field_simp

end Fabius
