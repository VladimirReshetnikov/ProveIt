import FabiusFunction.BasicHypergeometricSeries
import FabiusFunction.BaileyUnitPairs
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Divergence of nonterminating basic hypergeometric series

The complement of the convergence half of prop:phi-convergence.  For a nonterminating series
(`1 - a_i q^n ≠ 0` for all `i, n`) with `0 < ‖q‖ < 1`, `z ≠ 0` and nonvanishing denominators:

* if `r = s + 1` and `‖z‖ > 1`, the series diverges (`not_summable_basicHypergeometricTerm_of_eq`):
  the ratio of consecutive terms tends to `z` in norm, so the radius of convergence is exactly `1`;
* if `r > s + 1`, the terms are eventually increasing in norm, so they do not tend to zero and the
  series diverges (`not_summable_basicHypergeometricTerm_of_lt`,
  `not_tendsto_basicHypergeometricTerm_of_lt`): the ratio carries the factor `(-q^n)^{1+s-r}`,
  whose norm tends to infinity.

Both follow from the one-step ratio formula `basicHypergeometricTerm_succ`.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The one-step ratio of consecutive terms:
`t_{n+1} = t_n · ∏(1 - a_i q^n)/((1 - q^{n+1}) ∏(1 - b_j q^n)) · (-q^n)^{1+s-r} · z`. -/
theorem basicHypergeometricTerm_succ {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜) (q z : 𝕜)
    (n : ℕ) :
    basicHypergeometricTerm as bs q z (n + 1) =
      basicHypergeometricTerm as bs q z n *
        ((∏ i, (1 - as i * q ^ n)) / ((1 - q * q ^ n) * ∏ j, (1 - bs j * q ^ n)) *
          (-(q ^ n)) ^ ((1 + s : ℤ) - r) * z) := by
  have hc : (n + 1).choose 2 = n.choose 2 + n := by
    have h1 := two_mul_choose_two_int n
    have h2 := two_mul_choose_two_int (n + 1)
    push_cast at h1 h2
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    zify
    linear_combination h2 - h1
  have hE : ((-1 : 𝕜) ^ (n + 1) * q ^ (n + 1).choose 2) =
      ((-1) ^ n * q ^ n.choose 2) * (-(q ^ n)) := by
    rw [hc, pow_add, pow_succ]
    ring
  unfold basicHypergeometricTerm
  simp only [finiteQPochhammerIn_succ, prod_mul_distrib, div_eq_mul_inv, mul_inv]
  rw [hE, mul_zpow, pow_succ]
  ring

/-- Nonvanishing of the terms of a nonterminating series. -/
theorem basicHypergeometricTerm_ne_zero {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜) {q z : 𝕜}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz : z ≠ 0) (has : ∀ i n, 1 - as i * q ^ n ≠ 0)
    (hbs : ∀ j n, 1 - bs j * q ^ n ≠ 0) (n : ℕ) : basicHypergeometricTerm as bs q z n ≠ 0 := by
  have hfin : ∀ (a : 𝕜), (∀ m, 1 - a * q ^ m ≠ 0) → finiteQPochhammerIn a q n ≠ 0 := by
    intro a ha
    unfold finiteQPochhammerIn
    exact prod_ne_zero_iff.mpr fun m _ => ha m
  have hqq : ∀ m, (1 : 𝕜) - q * q ^ m ≠ 0 := fun m => by
    rw [← pow_succ']
    exact one_sub_ne_zero_of_norm_lt_one
      (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero m))
  unfold basicHypergeometricTerm
  refine mul_ne_zero (mul_ne_zero (div_ne_zero ?_ (mul_ne_zero (hfin q hqq) ?_)) ?_)
    (pow_ne_zero _ hz)
  · exact prod_ne_zero_iff.mpr fun i _ => hfin (as i) (has i)
  · exact prod_ne_zero_iff.mpr fun j _ => hfin (bs j) (hbs j)
  · exact zpow_ne_zero _ (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ hq0))

/-- The bracket `∏(1 - a_i q^n)/((1 - q^{n+1}) ∏(1 - b_j q^n))` tends to `1`. -/
theorem tendsto_basicHypergeometric_bracket {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜) {q : 𝕜}
    (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => (∏ i, (1 - as i * q ^ n)) / ((1 - q * q ^ n) * ∏ j, (1 - bs j * q ^ n)))
      atTop (𝓝 1) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have h1 : ∀ a : 𝕜, Tendsto (fun n : ℕ => 1 - a * q ^ n) atTop (𝓝 1) := fun a => by
    have := (hpow.const_mul a).const_sub (1 : 𝕜)
    simpa using this
  have hA : Tendsto (fun n : ℕ => ∏ i, (1 - as i * q ^ n)) atTop (𝓝 1) := by
    have := tendsto_finsetProd (univ : Finset (Fin r)) fun i _ => h1 (as i)
    simpa using this
  have hB : Tendsto (fun n : ℕ => ∏ j, (1 - bs j * q ^ n)) atTop (𝓝 1) := by
    have := tendsto_finsetProd (univ : Finset (Fin s)) fun j _ => h1 (bs j)
    simpa using this
  have h := hA.div ((h1 q).mul hB) (by norm_num)
  rw [one_mul, div_one] at h
  exact h

/-- **Divergence outside the unit disc for `r = s + 1`** (prop:phi-convergence (ii), the
divergence half): a nonterminating `ₛ₊₁φₛ` with `‖z‖ > 1` is not summable. -/
theorem not_summable_basicHypergeometricTerm_of_eq {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜)
    {q z : 𝕜} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hrs : r = s + 1) (hz : 1 < ‖z‖)
    (has : ∀ i n, 1 - as i * q ^ n ≠ 0) (hbs : ∀ j n, 1 - bs j * q ^ n ≠ 0) :
    ¬ Summable (basicHypergeometricTerm as bs q z) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans one_pos hz)
  have hne := basicHypergeometricTerm_ne_zero as bs hq0 hq hz0 has hbs
  have he : ((1 + s : ℤ) - r) = 0 := by rw [hrs]; push_cast; ring
  refine not_summable_of_ratio_test_tendsto_gt_one hz ?_
  have hratio : ∀ n, ‖basicHypergeometricTerm as bs q z (n + 1)‖ /
      ‖basicHypergeometricTerm as bs q z n‖ =
      ‖(∏ i, (1 - as i * q ^ n)) / ((1 - q * q ^ n) * ∏ j, (1 - bs j * q ^ n))‖ * ‖z‖ := by
    intro n
    rw [basicHypergeometricTerm_succ, he, zpow_zero, mul_one, norm_mul, norm_mul,
      mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr (hne n))]
  simp_rw [hratio]
  have := ((tendsto_basicHypergeometric_bracket as bs hq).norm).mul_const ‖z‖
  simpa using this

/-- For `r > s + 1`, `z ≠ 0`, the terms of a nonterminating series eventually at least double
in norm. -/
theorem eventually_two_mul_norm_le_basicHypergeometricTerm_succ {r s : ℕ} (as : Fin r → 𝕜)
    (bs : Fin s → 𝕜) {q z : 𝕜} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hrs : s + 1 < r) (hz : z ≠ 0) :
    ∀ᶠ n in atTop, 2 * ‖basicHypergeometricTerm as bs q z n‖ ≤
      ‖basicHypergeometricTerm as bs q z (n + 1)‖ := by
  obtain ⟨m, hm⟩ : ∃ m, r = s + 1 + (m + 1) := ⟨r - s - 2, by omega⟩
  have he : ((1 + s : ℤ) - r) = -((m + 1 : ℕ) : ℤ) := by rw [hm]; push_cast; ring
  have hq0' : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  -- the bracket is eventually at least `1/2` in norm
  have hbr : ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤
      ‖(∏ i, (1 - as i * q ^ n)) / ((1 - q * q ^ n) * ∏ j, (1 - bs j * q ^ n))‖ := by
    have h := (tendsto_basicHypergeometric_bracket as bs hq).norm
    rw [norm_one] at h
    exact h.eventually (eventually_ge_nhds (by norm_num))
  -- `(‖q‖^n)^{-(m+1)} ‖z‖` is eventually at least `4`
  have hpow : Tendsto (fun n : ℕ => (‖q‖⁻¹) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hq0' |>.mpr hq)
  have hbig : ∀ᶠ n in atTop, (4 : ℝ) ≤ (‖q‖ ^ n) ^ (-((m + 1 : ℕ) : ℤ)) * ‖z‖ := by
    filter_upwards [hpow.eventually_ge_atTop (4 / ‖z‖)] with n hn
    have h1 : (‖q‖ ^ n) ^ (-((m + 1 : ℕ) : ℤ)) = ((‖q‖ ^ n) ^ (m + 1))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have h2 : ((‖q‖ ^ n) ^ (m + 1))⁻¹ ≥ (‖q‖ ^ n)⁻¹ :=
      inv_anti₀ (pow_pos (pow_pos hq0' n) _)
        (pow_le_of_le_one (pow_pos hq0' n).le (pow_le_one₀ hq0'.le hq.le) (Nat.succ_ne_zero m))
    rw [h1]
    calc (4 : ℝ) = 4 / ‖z‖ * ‖z‖ := by field_simp
      _ ≤ (‖q‖⁻¹) ^ n * ‖z‖ := mul_le_mul_of_nonneg_right hn hz0.le
      _ = (‖q‖ ^ n)⁻¹ * ‖z‖ := by rw [inv_pow]
      _ ≤ ((‖q‖ ^ n) ^ (m + 1))⁻¹ * ‖z‖ := mul_le_mul_of_nonneg_right h2 hz0.le
  filter_upwards [hbr, hbig] with n hn1 hn2
  have key : 2 * ‖basicHypergeometricTerm as bs q z n‖ ≤
      ‖basicHypergeometricTerm as bs q z n‖ *
        (‖(∏ i, (1 - as i * q ^ n)) / ((1 - q * q ^ n) * ∏ j, (1 - bs j * q ^ n))‖ *
          ((‖q‖ ^ n) ^ (-((m + 1 : ℕ) : ℤ)) * ‖z‖)) := by
    calc 2 * ‖basicHypergeometricTerm as bs q z n‖
        = ‖basicHypergeometricTerm as bs q z n‖ * ((1 / 2) * 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hn1 hn2 (by norm_num) (norm_nonneg _))
          (norm_nonneg _)
  rw [basicHypergeometricTerm_succ, he]
  refine key.trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, norm_mul, norm_zpow, norm_neg, norm_pow]
  ring

/-- **Divergence for `r > s + 1`** (prop:phi-convergence (iii)): a nonterminating series with
`r > s + 1` and `z ≠ 0` is not summable. -/
theorem not_summable_basicHypergeometricTerm_of_lt {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜)
    {q z : 𝕜} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hrs : s + 1 < r) (hz : z ≠ 0)
    (has : ∀ i n, 1 - as i * q ^ n ≠ 0) (hbs : ∀ j n, 1 - bs j * q ^ n ≠ 0) :
    ¬ Summable (basicHypergeometricTerm as bs q z) :=
  not_summable_of_ratio_norm_eventually_ge one_lt_two
    (Eventually.frequently (Eventually.of_forall fun n =>
      norm_ne_zero_iff.mpr (basicHypergeometricTerm_ne_zero as bs hq0 hq hz has hbs n)))
    (eventually_two_mul_norm_le_basicHypergeometricTerm_succ as bs hq0 hq hrs hz)

/-- **The terms do not tend to zero for `r > s + 1`** (prop:phi-convergence (iii)). -/
theorem not_tendsto_basicHypergeometricTerm_of_lt {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜)
    {q z : 𝕜} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hrs : s + 1 < r) (hz : z ≠ 0)
    (has : ∀ i n, 1 - as i * q ^ n ≠ 0) (hbs : ∀ j n, 1 - bs j * q ^ n ≠ 0) :
    ¬ Tendsto (basicHypergeometricTerm as bs q z) atTop (𝓝 0) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_two_mul_norm_le_basicHypergeometricTerm_succ as bs hq0 hq hrs hz)
  have hmono : ∀ n, N ≤ n → ‖basicHypergeometricTerm as bs q z N‖ ≤
      ‖basicHypergeometricTerm as bs q z n‖ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih =>
        refine ih.trans ?_
        have := hN k hk
        linarith [norm_nonneg (basicHypergeometricTerm as bs q z k)]
  have hpos : 0 < ‖basicHypergeometricTerm as bs q z N‖ :=
    norm_pos_iff.mpr (basicHypergeometricTerm_ne_zero as bs hq0 hq hz has hbs N)
  have hn := h.norm
  rw [norm_zero] at hn
  have h2 := (tendsto_order.1 hn).2 _ hpos
  rw [eventually_atTop] at h2
  obtain ⟨M, hM⟩ := h2
  have := hM (max N M) (le_max_right _ _)
  have := hmono (max N M) (le_max_left _ _)
  linarith

end Fabius
