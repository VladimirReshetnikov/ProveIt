/-
# The Lie–Trotter product formula with its complete logarithmic error (Theorem 11.2)

This file formalizes Lemma 11.1 (for two factors) and Theorem 11.2 of the
accompanying article (`docs/combined`, Section 11), in a Banach algebra with
`‖1‖ = 1` as assumed there:

* `tsum_norm_bchHom_tail_two_le`, `tsum_norm_bchHom_tail_three_le` (Lemma 11.1):
  if `σ = ‖X‖ + ‖Y‖ < ½ log 2`, the terms of degree at least two of the BCH
  series have total norm at most `c₀ σ²`, and those of degree at least three
  at most `c₀' σ³`, with `c₀ = 4 (log 2)⁻² log(1/(2 - √2))` and
  `c₀' = 8 (log 2)⁻³ log(1/(2 - √2))`;
* `trotter_expansion` (equation (11.2)): for `n > |t| a / log 2`, `a = ‖X‖ + ‖Y‖`,
  `(e^{tX/n} e^{tY/n})^n = exp(t(X + Y) + ∑_{k ≥ 2} t^k n^{1-k} Zₖ(X, Y))`;
* `trotter_error`: for `n > 2 |t| a / log 2`,
  `‖(e^{tX/n} e^{tY/n})^n - e^{t(X+Y)}‖ ≤ e^{|t| a + c₀ t² a² / n} · c₀ t² a² / n`,
  the `O(n⁻¹)` bound of the article's proof, uniform for `t` in bounded sets;
* `trotter_limit` (equation (11.1)): `(e^{tX/n} e^{tY/n})^n → e^{t(X+Y)}` in norm.

The proofs combine the BCH theorem of `BCH.Series` (applied to `tX/n, tY/n`),
the homogeneity `Zₖ(cX, cY) = c^k Zₖ(X, Y)`, the identity `(e^L)^n = e^{nL}`,
and the exponential estimate of `BCH.Remainder`.
-/
import BCH.Remainder
import BCH.LowDegree

open NormedSpace Finset Filter Topology

namespace BCH

/-- The absolute constant `c₀ = 4 (log 2)⁻² log(1/(2 - √2))` of Lemma 11.1. -/
noncomputable def trotterC₀ : ℝ := 4 / Real.log 2 ^ 2 * Real.log (1 / (2 - Real.sqrt 2))

/-- The absolute constant `c₀' = 8 (log 2)⁻³ log(1/(2 - √2))` of Lemma 11.1. -/
noncomputable def trotterC₀' : ℝ := 8 / Real.log 2 ^ 3 * Real.log (1 / (2 - Real.sqrt 2))

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h : Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h

lemma one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
  rwa [Real.sqrt_one] at h

lemma two_sub_sqrt_two_pos : 0 < 2 - Real.sqrt 2 := by linarith [sqrt_two_lt_two]

lemma log_two_sub_sqrt_two_nonneg : 0 ≤ Real.log (1 / (2 - Real.sqrt 2)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ two_sub_sqrt_two_pos, one_mul]
  linarith [one_le_sqrt_two]

lemma trotterC₀_nonneg : 0 ≤ trotterC₀ :=
  mul_nonneg (by positivity) log_two_sub_sqrt_two_nonneg

lemma exp_half_log_two : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
  rw [Real.exp_half, Real.exp_log two_pos]

section Tail

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

lemma bchHom_zero_zero (n : ℕ) (hn : 0 < n) : bchHom 𝕂 (0 : 𝔸) 0 n = 0 := by
  have h := bchHom_smul (𝕂 := 𝕂) (0 : 𝕂) (0 : 𝔸) 0 n
  rwa [smul_zero, zero_pow hn.ne', zero_smul] at h

/-- **Lemma 11.1, quadratic bound** (two factors): if `‖X‖ + ‖Y‖ < ½ log 2`, the terms of
degree at least two of the BCH series have total norm at most `c₀ (‖X‖ + ‖Y‖)²`. -/
theorem tsum_norm_bchHom_tail_two_le (X Y : 𝔸) (hσ : ‖X‖ + ‖Y‖ < Real.log 2 / 2) :
    ∑' i, ‖bchHom 𝕂 X Y (i + 2)‖ ≤ trotterC₀ * (‖X‖ + ‖Y‖) ^ 2 := by
  have hσ0 : 0 ≤ ‖X‖ + ‖Y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  rcases hσ0.eq_or_lt with h0 | hpos
  · have hX : X = 0 := norm_eq_zero.mp (by linarith [norm_nonneg X, norm_nonneg Y])
    have hY : Y = 0 := norm_eq_zero.mp (by linarith [norm_nonneg X, norm_nonneg Y])
    subst hX hY
    simp [bchHom_zero_zero]
  · have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    set σ := ‖X‖ + ‖Y‖ with hσdef
    set ρ := Real.log 2 / (2 * σ) with hρdef
    have hρσ : ρ * σ = Real.log 2 / 2 := by
      rw [hρdef]; field_simp
    have hρ1 : 1 < ρ := by
      rw [hρdef, lt_div_iff₀ (by positivity)]; linarith
    have hs : ρ * σ < Real.log 2 := by rw [hρσ]; linarith
    have h := tsum_norm_bchHom_tail_le (𝕂 := 𝕂) X Y hρ1 hs 1
    rw [hρσ, exp_half_log_two] at h
    simp only [Nat.reduceAdd] at h
    refine h.trans (le_of_eq ?_)
    rw [hρdef, trotterC₀, one_div, Real.log_inv]
    field_simp
    ring

/-- **Lemma 11.1, cubic bound** (two factors): if `‖X‖ + ‖Y‖ < ½ log 2`, the terms of
degree at least three of the BCH series have total norm at most `c₀' (‖X‖ + ‖Y‖)³`. -/
theorem tsum_norm_bchHom_tail_three_le (X Y : 𝔸) (hσ : ‖X‖ + ‖Y‖ < Real.log 2 / 2) :
    ∑' i, ‖bchHom 𝕂 X Y (i + 3)‖ ≤ trotterC₀' * (‖X‖ + ‖Y‖) ^ 3 := by
  have hσ0 : 0 ≤ ‖X‖ + ‖Y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  rcases hσ0.eq_or_lt with h0 | hpos
  · have hX : X = 0 := norm_eq_zero.mp (by linarith [norm_nonneg X, norm_nonneg Y])
    have hY : Y = 0 := norm_eq_zero.mp (by linarith [norm_nonneg X, norm_nonneg Y])
    subst hX hY
    simp [bchHom_zero_zero]
  · have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    set σ := ‖X‖ + ‖Y‖ with hσdef
    set ρ := Real.log 2 / (2 * σ) with hρdef
    have hρσ : ρ * σ = Real.log 2 / 2 := by
      rw [hρdef]; field_simp
    have hρ1 : 1 < ρ := by
      rw [hρdef, lt_div_iff₀ (by positivity)]; linarith
    have hs : ρ * σ < Real.log 2 := by rw [hρσ]; linarith
    have h := tsum_norm_bchHom_tail_le (𝕂 := 𝕂) X Y hρ1 hs 2
    rw [hρσ, exp_half_log_two] at h
    simp only [Nat.reduceAdd] at h
    refine h.trans (le_of_eq ?_)
    rw [hρdef, trotterC₀', one_div, Real.log_inv]
    field_simp
    ring

end Tail

section Trotter

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
lemma trotter_scale_norm (X Y : 𝔸) (t : 𝕂) (n : ℕ) :
    ‖(t / n) • X‖ + ‖(t / n) • Y‖ = ‖t‖ * (‖X‖ + ‖Y‖) / n := by
  rw [norm_smul, norm_smul, ← mul_add, norm_div, RCLike.norm_natCast, div_mul_eq_mul_div]

omit [CompleteSpace 𝔸] in
/-- The logarithmic error of the Trotter product, `∑_{k ≥ 2} t^k n^{1-k} Zₖ(X, Y)`, equals
`n ∑_{k ≥ 2} Zₖ(tX/n, tY/n)`. -/
lemma trotter_tail_eq (X Y : 𝔸) (t : 𝕂) {n : ℕ} (hn : 0 < n) :
    ∑' k, (t ^ (k + 2) / (n : 𝕂) ^ (k + 1)) • bchHom 𝕂 X Y (k + 2) =
      (n : 𝕂) • ∑' k, bchHom 𝕂 ((t / n) • X) ((t / n) • Y) (k + 2) := by
  have hn' : (n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [← tsum_const_smul'' (n : 𝕂)]
  refine tsum_congr fun k => ?_
  rw [bchHom_smul, smul_smul]
  congr 1
  rw [div_pow]
  field_simp
  ring

/-- **Theorem 11.2, complete logarithmic error** (equation (11.2)): for `n > |t| a / log 2`,
`a = ‖X‖ + ‖Y‖`,
`(e^{tX/n} e^{tY/n})^n = exp(t(X + Y) + ∑_{k ≥ 2} t^k n^{1-k} Zₖ(X, Y))`. -/
theorem trotter_expansion (X Y : 𝔸) (t : 𝕂) {n : ℕ}
    (hn : ‖t‖ * (‖X‖ + ‖Y‖) < n * Real.log 2) :
    (exp ((t / n) • X) * exp ((t / n) • Y)) ^ n =
      exp (t • (X + Y) + ∑' k, (t ^ (k + 2) / (n : 𝕂) ^ (k + 1)) • bchHom 𝕂 X Y (k + 2)) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have : (0 : ℝ) ≤ ‖t‖ * (‖X‖ + ‖Y‖) := by positivity
      simp at hn
      linarith
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnorm : ‖(t / n) • X‖ + ‖(t / n) • Y‖ < Real.log 2 := by
    rw [trotter_scale_norm X Y t n, div_lt_iff₀ hnR]
    linarith
  have hbch := exp_tsum_bchHom (𝕂 := 𝕂) hnorm
  have hsum : Summable fun k => bchHom 𝕂 ((t / n) • X) ((t / n) • Y) k :=
    (summable_norm_bchHom (𝕂 := 𝕂) hnorm).of_norm
  rw [← hbch, ← exp_nsmul]
  congr 1
  rw [trotter_tail_eq X Y t hn0, hsum.tsum_eq_zero_add,
    ((summable_nat_add_iff 1).2 hsum).tsum_eq_zero_add, bchHom_zero, zero_add, smul_add]
  congr 1
  · rw [zero_add, bchHom_one]
    simp only [← Nat.cast_smul_eq_nsmul 𝕂, smul_add, smul_smul]
    have hc : (n : 𝕂) * (t / n) = t := by
      rw [mul_div_assoc', mul_div_cancel_left₀ t (Nat.cast_ne_zero.mpr hn0.ne')]
    rw [hc]
  · rw [← Nat.cast_smul_eq_nsmul 𝕂]
    try rfl

/-- **Theorem 11.2, explicit error bound**: in a Banach algebra with `‖1‖ = 1`, for
`n > 2 |t| a / log 2`, `a = ‖X‖ + ‖Y‖`,
`‖(e^{tX/n} e^{tY/n})^n - e^{t(X+Y)}‖ ≤ e^{|t| a + c₀ t² a² / n} · c₀ t² a² / n`. -/
theorem trotter_error [NormOneClass 𝔸] (X Y : 𝔸) (t : 𝕂) {n : ℕ}
    (hn : 2 * ‖t‖ * (‖X‖ + ‖Y‖) < n * Real.log 2) :
    ‖(exp ((t / n) • X) * exp ((t / n) • Y)) ^ n - exp (t • (X + Y))‖ ≤
      Real.exp (‖t‖ * (‖X‖ + ‖Y‖) + trotterC₀ * ‖t‖ ^ 2 * (‖X‖ + ‖Y‖) ^ 2 / n) *
        (trotterC₀ * ‖t‖ ^ 2 * (‖X‖ + ‖Y‖) ^ 2 / n) := by
  set a := ‖X‖ + ‖Y‖ with ha
  have ha0 : 0 ≤ a := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hta : 0 ≤ ‖t‖ * a := mul_nonneg (norm_nonneg _) ha0
  have hn' : ‖t‖ * a < n * Real.log 2 := by linarith
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hn'; linarith
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [trotter_expansion X Y t hn']
  set E := ∑' k, (t ^ (k + 2) / (n : 𝕂) ^ (k + 1)) • bchHom 𝕂 X Y (k + 2) with hE
  -- the tail bound for the scaled elements
  have hσ : ‖(t / n) • X‖ + ‖(t / n) • Y‖ < Real.log 2 / 2 := by
    rw [trotter_scale_norm X Y t n, div_lt_iff₀ hnR]
    linarith
  have hEle : ‖E‖ ≤ trotterC₀ * ‖t‖ ^ 2 * a ^ 2 / n := by
    have htail := tsum_norm_bchHom_tail_two_le (𝕂 := 𝕂) ((t / n) • X) ((t / n) • Y) hσ
    rw [trotter_scale_norm X Y t n] at htail
    have hsum : Summable fun k => ‖bchHom 𝕂 ((t / n) • X) ((t / n) • Y) (k + 2)‖ :=
      (summable_nat_add_iff 2 (f := fun k => ‖bchHom 𝕂 ((t / n) • X) ((t / n) • Y) k‖)).2
        (summable_norm_bchHom (𝕂 := 𝕂) (by linarith [hσ, Real.log_pos one_lt_two]))
    rw [hE, trotter_tail_eq X Y t hn0, norm_smul, RCLike.norm_natCast]
    calc (n : ℝ) * ‖∑' k, bchHom 𝕂 ((t / n) • X) ((t / n) • Y) (k + 2)‖
        ≤ (n : ℝ) * ∑' k, ‖bchHom 𝕂 ((t / n) • X) ((t / n) • Y) (k + 2)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsum) hnR.le
      _ ≤ (n : ℝ) * (trotterC₀ * (‖t‖ * a / n) ^ 2) := mul_le_mul_of_nonneg_left htail hnR.le
      _ = trotterC₀ * ‖t‖ ^ 2 * a ^ 2 / n := by field_simp
  have hbound := norm_exp_sub_exp_le 𝕂 (t • (X + Y)) (t • (X + Y) + E)
  rw [norm_one, one_pow, one_mul, add_sub_cancel_left] at hbound
  refine hbound.trans ?_
  have hS : ‖t • (X + Y)‖ ≤ ‖t‖ * a := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
  have hmax : max ‖t • (X + Y)‖ ‖t • (X + Y) + E‖ ≤ ‖t‖ * a + ‖E‖ :=
    max_le (by linarith [norm_nonneg E]) ((norm_add_le _ _).trans (by linarith))
  exact mul_le_mul (Real.exp_le_exp.mpr (hmax.trans (by linarith))) hEle (norm_nonneg _)
    (Real.exp_pos _).le

/-- **Theorem 11.2, the Lie–Trotter product formula** (equation (11.1)): in a Banach algebra
with `‖1‖ = 1`, `(e^{tX/n} e^{tY/n})^n → e^{t(X+Y)}` in norm as `n → ∞`. -/
theorem trotter_limit [NormOneClass 𝔸] (X Y : 𝔸) (t : 𝕂) :
    Tendsto (fun n : ℕ => (exp ((t / n) • X) * exp ((t / n) • Y)) ^ n) atTop
      (𝓝 (exp (t • (X + Y)))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq0 : 0 ≤ trotterC₀ * ‖t‖ ^ 2 * (‖X‖ + ‖Y‖) ^ 2 := by
    have := trotterC₀_nonneg
    positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat
      (Real.exp (‖t‖ * (‖X‖ + ‖Y‖) + trotterC₀ * ‖t‖ ^ 2 * (‖X‖ + ‖Y‖) ^ 2) *
        (trotterC₀ * ‖t‖ ^ 2 * (‖X‖ + ‖Y‖) ^ 2)))
  filter_upwards [eventually_gt_atTop ⌈2 * ‖t‖ * (‖X‖ + ‖Y‖) / Real.log 2⌉₊,
    eventually_ge_atTop 1] with n hn hn1
  have hn' : 2 * ‖t‖ * (‖X‖ + ‖Y‖) < n * Real.log 2 := by
    have h1 : 2 * ‖t‖ * (‖X‖ + ‖Y‖) / Real.log 2 < n :=
      (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    rw [div_lt_iff₀ hlog2] at h1
    linarith
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  refine (trotter_error X Y t hn').trans ?_
  calc _ ≤ Real.exp (‖t‖ * (‖X‖ + ‖Y‖) + trotterC₀ * ‖t‖ ^ 2 * (‖X‖ + ‖Y‖) ^ 2) *
        (trotterC₀ * ‖t‖ ^ 2 * (‖X‖ + ‖Y‖) ^ 2 / n) :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith [div_le_self hq0 hn1R])) (by positivity)
    _ = _ := (mul_div_assoc _ _ _).symm

end Trotter

end BCH
