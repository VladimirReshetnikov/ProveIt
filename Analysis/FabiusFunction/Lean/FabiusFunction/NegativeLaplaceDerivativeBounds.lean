import FabiusFunction.LaplaceMomentBounds
import Mathlib.Data.Nat.Log

/-!
# Quantitative bounds for negative-Laplace logarithmic derivatives

Differentiating the exact dilation equation for the negative-Laplace
logarithm gives a dyadic recurrence for each of its first four derivatives.
This module supplies explicit derivatives and polynomially weighted bounds
for the elementary dilation kernel, then iterates those recurrences to prove

`q⁽ʲ⁾(n) = O(log n / nʲ)`, for `1 ≤ j ≤ 4`,

along the natural numbers. These are the cumulant bounds used in the sharp
dyadic endpoint expansion.
-/

set_option autoImplicit false

open Filter Set Topology Asymptotics

namespace Fabius

noncomputable def negativeLaplaceKernelFirst (x : ℝ) : ℝ :=
  Real.exp (-x) / (1 - Real.exp (-x)) - 1 / x

noncomputable def negativeLaplaceKernelSecond (x : ℝ) : ℝ :=
  -Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 + 1 / x ^ 2

noncomputable def negativeLaplaceKernelThird (x : ℝ) : ℝ :=
  Real.exp (-x) * (1 + Real.exp (-x)) /
      (1 - Real.exp (-x)) ^ 3 - 2 / x ^ 3

noncomputable def negativeLaplaceKernelFourth (x : ℝ) : ℝ :=
  -(Real.exp (-x) *
      (1 + 4 * Real.exp (-x) + Real.exp (-x) ^ 2)) /
      (1 - Real.exp (-x)) ^ 4 + 6 / x ^ 4

private lemma one_sub_exp_neg_ne {x : ℝ} (hx : 0 < x) :
    1 - Real.exp (-x) ≠ 0 := by
  apply (sub_pos.mpr ?_).ne'
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem negativeLaplaceKernel_hasDerivAt
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt negativeLaplaceKernel (negativeLaplaceKernelFirst x) x := by
  have ht := (hasDerivAt_id x).neg.exp
  have hnum := (hasDerivAt_const x 1).sub ht
  have hlognum := hnum.log (one_sub_exp_neg_ne hx)
  have hlogx := (hasDerivAt_id x).log hx.ne'
  have h := hlognum.sub hlogx
  have h' : HasDerivAt
      (fun y => Real.log (1 - Real.exp (-y)) - Real.log y) _ x :=
    h.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
  have heq : negativeLaplaceKernel =ᶠ[nhds x]
      (fun y => Real.log (1 - Real.exp (-y)) - Real.log y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    unfold negativeLaplaceKernel
    rw [Real.log_div (one_sub_exp_neg_ne hy) hy.ne']
  have hc := h'.congr_of_eventuallyEq heq
  refine hc.congr_deriv ?_
  unfold negativeLaplaceKernelFirst
  simp only [id_eq, Pi.neg_apply, Pi.sub_apply]
  ring

theorem negativeLaplaceKernelFirst_hasDerivAt
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt negativeLaplaceKernelFirst (negativeLaplaceKernelSecond x) x := by
  have ht := (hasDerivAt_id x).neg.exp
  have hnum := (hasDerivAt_const x 1).sub ht
  have hquot := ht.div hnum (one_sub_exp_neg_ne hx)
  have hinv := (hasDerivAt_const x 1).div (hasDerivAt_id x) hx.ne'
  have h := hquot.sub hinv
  refine h.congr_deriv ?_
  unfold negativeLaplaceKernelSecond
  simp only [id_eq, Pi.neg_apply, Pi.sub_apply]
  field_simp [one_sub_exp_neg_ne hx, hx.ne']
  ring

theorem negativeLaplaceKernelSecond_hasDerivAt
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt negativeLaplaceKernelSecond (negativeLaplaceKernelThird x) x := by
  have ht := (hasDerivAt_id x).neg.exp
  have hnum := (hasDerivAt_const x 1).sub ht
  have hfrac := ht.neg.div (hnum.pow 2) (pow_ne_zero 2 (one_sub_exp_neg_ne hx))
  have hx2 := (hasDerivAt_id x).pow 2
  have hone := (hasDerivAt_const x 1).div hx2 (pow_ne_zero 2 hx.ne')
  have h := hfrac.add hone
  refine h.congr_deriv ?_
  unfold negativeLaplaceKernelThird
  simp only [id_eq, Pi.neg_apply, Pi.sub_apply, Pi.pow_apply]
  field_simp [one_sub_exp_neg_ne hx, hx.ne']
  ring

theorem negativeLaplaceKernelThird_hasDerivAt
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt negativeLaplaceKernelThird (negativeLaplaceKernelFourth x) x := by
  have ht := (hasDerivAt_id x).neg.exp
  have hnum := (hasDerivAt_const x 1).sub ht
  have hplus := (hasDerivAt_const x 1).add ht
  have hfrac := (ht.mul hplus).div (hnum.pow 3)
    (pow_ne_zero 3 (one_sub_exp_neg_ne hx))
  have hx3 := (hasDerivAt_id x).pow 3
  have htwo := (hasDerivAt_const x 2).div hx3 (pow_ne_zero 3 hx.ne')
  have h := hfrac.sub htwo
  refine h.congr_deriv ?_
  unfold negativeLaplaceKernelFourth
  simp only [id_eq, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
    Pi.pow_apply]
  field_simp [one_sub_exp_neg_ne hx, hx.ne']
  ring

private lemma pow_mul_exp_neg_le_factorial
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-x) ≤ (k.factorial : ℝ) := by
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hseries := Real.pow_div_factorial_le_exp x hx k
  have hmul := mul_le_mul_of_nonneg_right hseries (Real.exp_nonneg (-x))
  rw [div_mul_eq_mul_div] at hmul
  rw [← Real.exp_add] at hmul
  norm_num at hmul
  rwa [div_le_one hfac] at hmul

private lemma exp_neg_le_half {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-x) ≤ 1 / 2 := by
  calc
    Real.exp (-x) ≤ Real.exp (-1) := by
      exact Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le

private lemma exp_neg_div_one_sub_pow_le
    (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-x) / (1 - Real.exp (-x)) ^ m ≤
      2 ^ m * Real.exp (-x) := by
  let t := Real.exp (-x)
  have ht0 : 0 ≤ t := Real.exp_nonneg _
  have ht : t ≤ 1 / 2 := exp_neg_le_half hx
  have hden : 0 < 1 - t := by linarith
  rw [div_le_iff₀ (pow_pos hden m)]
  have hbase : 1 ≤ 2 * (1 - t) := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hbase m
  rw [one_pow, mul_pow] at hp
  simpa [t, mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left hp ht0)

theorem abs_mul_negativeLaplaceKernelFirst_le
    {x : ℝ} (hx : 1 ≤ x) :
    |x * negativeLaplaceKernelFirst x| ≤ 3 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht0 : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
  have hden : 0 < 1 - Real.exp (-x) := by
    linarith [exp_neg_le_half hx]
  have hfrac := exp_neg_div_one_sub_pow_le 1 hx
  norm_num at hfrac
  have hpow := pow_mul_exp_neg_le_factorial 1 hx0.le
  unfold negativeLaplaceKernelFirst
  rw [abs_mul, abs_of_pos hx0]
  calc
    x * |Real.exp (-x) / (1 - Real.exp (-x)) - 1 / x| ≤
        x * (|Real.exp (-x) / (1 - Real.exp (-x))| + |1 / x|) := by
      gcongr
      exact abs_sub _ _
    _ = x * (Real.exp (-x) / (1 - Real.exp (-x)) + 1 / x) := by
      rw [abs_of_nonneg (div_nonneg ht0 hden.le), abs_of_pos (one_div_pos.mpr hx0)]
    _ ≤ x * (2 * Real.exp (-x) + 1 / x) := by gcongr
    _ ≤ 3 := by
      have hxinv : x * (1 / x) = 1 := by field_simp
      norm_num at hpow
      nlinarith

theorem abs_sq_mul_negativeLaplaceKernelSecond_le
    {x : ℝ} (hx : 1 ≤ x) :
    |x ^ 2 * negativeLaplaceKernelSecond x| ≤ 9 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht0 : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
  have hden : 0 < 1 - Real.exp (-x) := by
    linarith [exp_neg_le_half hx]
  have hfrac := exp_neg_div_one_sub_pow_le 2 hx
  have hpow := pow_mul_exp_neg_le_factorial 2 hx0.le
  unfold negativeLaplaceKernelSecond
  rw [abs_mul, abs_of_pos (sq_pos_of_pos hx0)]
  calc
    x ^ 2 * |-Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 + 1 / x ^ 2| ≤
        x ^ 2 * (|-Real.exp (-x) / (1 - Real.exp (-x)) ^ 2| +
          |1 / x ^ 2|) := by
      gcongr
      exact abs_add_le _ _
    _ = x ^ 2 * (Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 +
          1 / x ^ 2) := by
      rw [abs_div, abs_neg, abs_of_pos (Real.exp_pos _),
        abs_of_pos (pow_pos hden 2),
        abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hx0))]
    _ ≤ x ^ 2 * (4 * Real.exp (-x) + 1 / x ^ 2) := by
      norm_num at hfrac
      gcongr
    _ ≤ 9 := by
      have hxinv : x ^ 2 * (1 / x ^ 2) = 1 := by field_simp
      norm_num at hpow
      nlinarith

theorem abs_cube_mul_negativeLaplaceKernelThird_le
    {x : ℝ} (hx : 1 ≤ x) :
    |x ^ 3 * negativeLaplaceKernelThird x| ≤ 74 := by
  let t := Real.exp (-x)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht0 : 0 ≤ t := Real.exp_nonneg _
  have ht : t ≤ 1 / 2 := exp_neg_le_half hx
  have hden : 0 < 1 - t := by linarith
  have hfrac := exp_neg_div_one_sub_pow_le 3 hx
  norm_num at hfrac
  change t / (1 - t) ^ 3 ≤ 8 * t at hfrac
  have hterm : t * (1 + t) / (1 - t) ^ 3 ≤ 12 * t := by
    calc
      t * (1 + t) / (1 - t) ^ 3 = t / (1 - t) ^ 3 * (1 + t) := by ring
      _ ≤ (8 * t) * (3 / 2) := by
        gcongr
        linarith
      _ = 12 * t := by ring
  have hterm0 : 0 ≤ t * (1 + t) / (1 - t) ^ 3 := by positivity
  have hpow := pow_mul_exp_neg_le_factorial 3 hx0.le
  unfold negativeLaplaceKernelThird
  change |x ^ 3 * (t * (1 + t) / (1 - t) ^ 3 - 2 / x ^ 3)| ≤ 74
  rw [abs_mul, abs_of_pos (pow_pos hx0 3)]
  calc
    x ^ 3 * |t * (1 + t) / (1 - t) ^ 3 - 2 / x ^ 3| ≤
        x ^ 3 * (|t * (1 + t) / (1 - t) ^ 3| + |2 / x ^ 3|) := by
      gcongr
      exact abs_sub _ _
    _ = x ^ 3 * (t * (1 + t) / (1 - t) ^ 3 + 2 / x ^ 3) := by
      rw [abs_of_nonneg hterm0,
        abs_of_pos (div_pos (by norm_num) (pow_pos hx0 3))]
    _ ≤ x ^ 3 * (12 * t + 2 / x ^ 3) := by gcongr
    _ ≤ 74 := by
      have hxinv : x ^ 3 * (2 / x ^ 3) = 2 := by field_simp
      change x ^ 3 * Real.exp (-x) ≤ (Nat.factorial 3 : ℝ) at hpow
      norm_num at hpow
      nlinarith

theorem abs_fourth_mul_negativeLaplaceKernelFourth_le
    {x : ℝ} (hx : 1 ≤ x) :
    |x ^ 4 * negativeLaplaceKernelFourth x| ≤ 1542 := by
  let t := Real.exp (-x)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht0 : 0 ≤ t := Real.exp_nonneg _
  have ht : t ≤ 1 / 2 := exp_neg_le_half hx
  have hden : 0 < 1 - t := by linarith
  have hfrac := exp_neg_div_one_sub_pow_le 4 hx
  norm_num at hfrac
  change t / (1 - t) ^ 4 ≤ 16 * t at hfrac
  have hpoly : 1 + 4 * t + t ^ 2 ≤ 4 := by nlinarith [sq_nonneg t]
  have hterm : t * (1 + 4 * t + t ^ 2) / (1 - t) ^ 4 ≤ 64 * t := by
    calc
      t * (1 + 4 * t + t ^ 2) / (1 - t) ^ 4 =
          t / (1 - t) ^ 4 * (1 + 4 * t + t ^ 2) := by ring
      _ ≤ (16 * t) * 4 := by gcongr
      _ = 64 * t := by ring
  have hterm0 : 0 ≤ t * (1 + 4 * t + t ^ 2) / (1 - t) ^ 4 := by positivity
  have hpow := pow_mul_exp_neg_le_factorial 4 hx0.le
  unfold negativeLaplaceKernelFourth
  change |x ^ 4 * (-(t * (1 + 4 * t + t ^ 2)) / (1 - t) ^ 4 +
    6 / x ^ 4)| ≤ 1542
  rw [abs_mul, abs_of_pos (pow_pos hx0 4)]
  calc
    x ^ 4 * |-(t * (1 + 4 * t + t ^ 2)) / (1 - t) ^ 4 + 6 / x ^ 4| ≤
        x ^ 4 * (|-(t * (1 + 4 * t + t ^ 2)) / (1 - t) ^ 4| +
          |6 / x ^ 4|) := by
      gcongr
      exact abs_add_le _ _
    _ = x ^ 4 * (t * (1 + 4 * t + t ^ 2) / (1 - t) ^ 4 +
          6 / x ^ 4) := by
      rw [abs_div, abs_neg, abs_of_nonneg (mul_nonneg ht0 (by positivity)),
        abs_of_pos (pow_pos hden 4),
        abs_of_pos (div_pos (by norm_num) (pow_pos hx0 4))]
    _ ≤ x ^ 4 * (64 * t + 6 / x ^ 4) := by gcongr
    _ ≤ 1542 := by
      have hxinv : x ^ 4 * (6 / x ^ 4) = 6 := by field_simp
      change x ^ 4 * Real.exp (-x) ≤ (Nat.factorial 4 : ℝ) at hpow
      norm_num at hpow
      nlinarith

theorem negativeLaplaceLogFirst_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) :
    2 * negativeLaplaceLogFirst F (2 * s) =
      negativeLaplaceKernelFirst s + negativeLaplaceLogFirst F s := by
  have h2s : 0 < 2 * s := by positivity
  have hl := (negativeLaplaceLog_hasDerivAt F hF h2s).comp s
    ((hasDerivAt_id s).const_mul 2)
  have hr := (negativeLaplaceKernel_hasDerivAt hs).add
    (negativeLaplaceLog_hasDerivAt F hF hs)
  have heq : (fun x => negativeLaplaceLog (2 * x)) =ᶠ[nhds s]
      (fun x => negativeLaplaceKernel x + negativeLaplaceLog x) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact negativeLaplaceLog_two_mul x hx
  have hr' := hr.congr_of_eventuallyEq heq
  have hu := hl.unique hr'
  convert hu using 1
  ring

theorem negativeLaplaceLogSecond_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) :
    4 * negativeLaplaceLogSecond F (2 * s) =
      negativeLaplaceKernelSecond s + negativeLaplaceLogSecond F s := by
  have h2s : 0 < 2 * s := by positivity
  have hl := ((negativeLaplaceLogFirst_hasDerivAt F hF h2s).comp s
    ((hasDerivAt_id s).const_mul 2)).const_mul 2
  have hr := (negativeLaplaceKernelFirst_hasDerivAt hs).add
    (negativeLaplaceLogFirst_hasDerivAt F hF hs)
  have heq : (fun x => 2 * negativeLaplaceLogFirst F (2 * x)) =ᶠ[nhds s]
      (fun x => negativeLaplaceKernelFirst x + negativeLaplaceLogFirst F x) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact negativeLaplaceLogFirst_two_mul F hF hx
  have hr' := hr.congr_of_eventuallyEq heq
  have hu := hl.unique hr'
  convert hu using 1
  ring

theorem negativeLaplaceLogThird_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) :
    8 * negativeLaplaceLogThird F (2 * s) =
      negativeLaplaceKernelThird s + negativeLaplaceLogThird F s := by
  have h2s : 0 < 2 * s := by positivity
  have hl := ((negativeLaplaceLogSecond_hasDerivAt F hF h2s).comp s
    ((hasDerivAt_id s).const_mul 2)).const_mul 4
  have hr := (negativeLaplaceKernelSecond_hasDerivAt hs).add
    (negativeLaplaceLogSecond_hasDerivAt F hF hs)
  have heq : (fun x => 4 * negativeLaplaceLogSecond F (2 * x)) =ᶠ[nhds s]
      (fun x => negativeLaplaceKernelSecond x + negativeLaplaceLogSecond F x) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact negativeLaplaceLogSecond_two_mul F hF hx
  have hr' := hr.congr_of_eventuallyEq heq
  have hu := hl.unique hr'
  convert hu using 1
  ring

theorem negativeLaplaceLogFourth_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) :
    16 * negativeLaplaceLogFourth F (2 * s) =
      negativeLaplaceKernelFourth s + negativeLaplaceLogFourth F s := by
  have h2s : 0 < 2 * s := by positivity
  have hl := ((negativeLaplaceLogThird_hasDerivAt F hF h2s).comp s
    ((hasDerivAt_id s).const_mul 2)).const_mul 8
  have hr := (negativeLaplaceKernelThird_hasDerivAt hs).add
    (negativeLaplaceLogThird_hasDerivAt F hF hs)
  have heq : (fun x => 8 * negativeLaplaceLogThird F (2 * x)) =ᶠ[nhds s]
      (fun x => negativeLaplaceKernelThird x + negativeLaplaceLogThird F x) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact negativeLaplaceLogThird_two_mul F hF hx
  have hr' := hr.congr_of_eventuallyEq heq
  have hu := hl.unique hr'
  convert hu using 1
  ring

private theorem dyadic_recurrence_isBigO_nat
    (j : ℕ) (f g : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcont : ContinuousOn (fun s => |s ^ j * f s|) (Icc (1 : ℝ) 2))
    (hrec : ∀ {s : ℝ}, 0 < s →
      (2 : ℝ) ^ j * f (2 * s) = g s + f s)
    (hg : ∀ {s : ℝ}, 1 ≤ s → |s ^ j * g s| ≤ C) :
    (fun n : ℕ => f n) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ j) := by
  obtain ⟨A₀, hA₀⟩ := bddAbove_def.mp (isCompact_Icc.bddAbove_image hcont)
  let A : ℝ := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hbase : ∀ {s : ℝ}, 1 ≤ s → s ≤ 2 → |s ^ j * f s| ≤ A := by
    intro s hs1 hs2
    exact (hA₀ _ ⟨s, ⟨hs1, hs2⟩, rfl⟩).trans (le_max_left _ _)
  have hinterval : ∀ m : ℕ, ∀ {s : ℝ}, 1 ≤ s →
      s ≤ (2 : ℝ) ^ (m + 1) →
      |s ^ j * f s| ≤ A + (m + 1 : ℕ) * C := by
    intro m
    induction m with
    | zero =>
        intro s hs1 hs2
        norm_num at hs2
        calc
          |s ^ j * f s| ≤ A := hbase hs1 hs2
          _ ≤ A + (0 + 1 : ℕ) * C := by norm_num; positivity
    | succ m ih =>
        intro s hs1 hsupper
        by_cases hs2 : s ≤ 2
        · have hb := hbase hs1 hs2
          calc
            |s ^ j * f s| ≤ A := hb
            _ ≤ A + (m + 1 + 1 : ℕ) * C := by
              exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hC)
        · let t : ℝ := s / 2
          have ht1 : 1 ≤ t := by dsimp [t]; linarith
          have htupper : t ≤ (2 : ℝ) ^ (m + 1) := by
            dsimp [t]
            rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ] at hsupper
            nlinarith
          have hi := ih ht1 htupper
          have hgt := hg ht1
          have hrt := hrec (show 0 < t by linarith)
          have hst : s = 2 * t := by dsimp [t]; ring
          have heq : s ^ j * f s = t ^ j * (g t + f t) := by
            rw [hst]
            calc
              (2 * t) ^ j * f (2 * t) =
                  t ^ j * ((2 : ℝ) ^ j * f (2 * t)) := by rw [mul_pow]; ring
              _ = t ^ j * (g t + f t) := by rw [hrt]
          rw [heq, mul_add]
          calc
            |t ^ j * g t + t ^ j * f t| ≤
                |t ^ j * g t| + |t ^ j * f t| := abs_add_le _ _
            _ ≤ C + (A + (m + 1 : ℕ) * C) := add_le_add hgt hi
            _ = A + (m + 1 + 1 : ℕ) * C := by push_cast; ring
  have hlogPoint : ∀ n : ℕ, 2 ≤ n →
      |(n : ℝ) ^ j * f n| ≤
        A + (Nat.log 2 n + 1 : ℕ) * C := by
    intro n hn
    apply hinterval (Nat.log 2 n)
    · exact_mod_cast (show 1 ≤ n by omega)
    · exact_mod_cast (Nat.lt_pow_succ_log_self (by omega : 1 < 2) n).le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D : ℝ := A / Real.log 2 + 2 * C / Real.log 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply IsBigO.of_bound D
  filter_upwards [eventually_atTop.2 ⟨2, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : Real.log 2 ≤ Real.log (n : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hn0
      (by exact_mod_cast hn)
  have hpowNat := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hpowReal : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have hlogmono := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n by positivity)
      (show (0 : ℝ) < n from hn0)
      (by exact_mod_cast hpowNat : ((2 : ℝ) ^ Nat.log 2 n) ≤ n)
    rw [Real.log_pow] at hlogmono
    simpa [mul_comm] using hlogmono
  have hNatLog : (Nat.log 2 n + 1 : ℕ) * C ≤
      (2 * C / Real.log 2) * Real.log (n : ℝ) := by
    push_cast
    have hratio : (Nat.log 2 n : ℝ) + 1 ≤
        2 * Real.log (n : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hratio hC
    calc
      ((Nat.log 2 n : ℝ) + 1) * C ≤
          (2 * Real.log (n : ℝ) / Real.log 2) * C := hm
      _ = (2 * C / Real.log 2) * Real.log (n : ℝ) := by ring
  have hAlog : A ≤ A / Real.log 2 * Real.log (n : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  have hscaled := hlogPoint n hn
  rw [Real.norm_eq_abs]
  have hnPow : 0 < (n : ℝ) ^ j := pow_pos hn0 _
  have htarget0 : 0 ≤ Real.log (n : ℝ) / (n : ℝ) ^ j := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) hnPow.le
  rw [Real.norm_eq_abs, abs_of_nonneg htarget0]
  rw [← mul_div_assoc, le_div_iff₀ hnPow]
  calc
    |f n| * (n : ℝ) ^ j = |(n : ℝ) ^ j * f n| := by
      rw [abs_mul, abs_of_pos hnPow]
      ring
    _ ≤ A + (Nat.log 2 n + 1 : ℕ) * C := hscaled
    _ ≤ (A / Real.log 2 + 2 * C / Real.log 2) * Real.log (n : ℝ) := by
      nlinarith
    _ = D * Real.log (n : ℝ) := rfl

theorem negativeLaplaceLogFirst_isBigO_log_div_nat
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => negativeLaplaceLogFirst F n) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) := by
  have hq : ContinuousOn (negativeLaplaceLogFirst F) (Icc (1 : ℝ) 2) := by
      intro s hs
      exact (negativeLaplaceLogFirst_hasDerivAt F hF
        (zero_lt_one.trans_le hs.1)).continuousAt.continuousWithinAt
  have h := dyadic_recurrence_isBigO_nat 1
    (negativeLaplaceLogFirst F) negativeLaplaceKernelFirst 3 (by norm_num)
    (by simpa only [pow_one, Pi.mul_apply, id_eq] using (continuousOn_id.mul hq).abs)
    (by intro s hs
        simpa only [pow_one] using negativeLaplaceLogFirst_two_mul F hF hs)
    (by intro s hs
        simpa only [pow_one] using abs_mul_negativeLaplaceKernelFirst_le hs)
  simpa only [pow_one] using h

theorem negativeLaplaceLogSecond_isBigO_log_div_sq_nat
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => negativeLaplaceLogSecond F n) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
  apply dyadic_recurrence_isBigO_nat 2
    (negativeLaplaceLogSecond F) negativeLaplaceKernelSecond 9 (by norm_num)
  · have hq : ContinuousOn (negativeLaplaceLogSecond F) (Icc (1 : ℝ) 2) := by
      intro s hs
      exact (negativeLaplaceLogSecond_hasDerivAt F hF
        (zero_lt_one.trans_le hs.1)).continuousAt.continuousWithinAt
    exact ((continuousOn_id.pow 2).mul hq).abs
  · intro s hs
    norm_num
    exact negativeLaplaceLogSecond_two_mul F hF hs
  · intro s hs
    exact abs_sq_mul_negativeLaplaceKernelSecond_le hs

theorem negativeLaplaceLogThird_isBigO_log_div_cube_nat
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => negativeLaplaceLogThird F n) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 3) := by
  apply dyadic_recurrence_isBigO_nat 3
    (negativeLaplaceLogThird F) negativeLaplaceKernelThird 74 (by norm_num)
  · have hq : ContinuousOn (negativeLaplaceLogThird F) (Icc (1 : ℝ) 2) := by
      intro s hs
      exact (negativeLaplaceLogThird_hasDerivAt F hF
        (zero_lt_one.trans_le hs.1)).continuousAt.continuousWithinAt
    exact ((continuousOn_id.pow 3).mul hq).abs
  · intro s hs
    norm_num
    exact negativeLaplaceLogThird_two_mul F hF hs
  · intro s hs
    exact abs_cube_mul_negativeLaplaceKernelThird_le hs

theorem continuousOn_negativeLaplaceLogFourth_Icc
    (F : BoundedFabius) (hF : IsFabius F) :
    ContinuousOn (negativeLaplaceLogFourth F) (Icc (1 : ℝ) 2) := by
  intro s hs
  have hs0 : 0 < s := zero_lt_one.trans_le hs.1
  have h1 := (normalizedLaplaceMoment_hasDerivAt F hF 1 hs0).continuousAt
  have h2 := (normalizedLaplaceMoment_hasDerivAt F hF 2 hs0).continuousAt
  have h3 := (normalizedLaplaceMoment_hasDerivAt F hF 3 hs0).continuousAt
  have h4 := (normalizedLaplaceMoment_hasDerivAt F hF 4 hs0).continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold negativeLaplaceLogFourth
  have hc := (((h4.sub ((h1.const_mul 4).mul h3)).sub
    ((h2.pow 2).const_mul 3)).add (((h1.pow 2).const_mul 12).mul h2)).sub
      ((h1.pow 4).const_mul 6)
  apply hc.congr_of_eventuallyEq
  filter_upwards with x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]

theorem negativeLaplaceLogFourth_isBigO_log_div_fourth_nat
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => negativeLaplaceLogFourth F n) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ 4) := by
  apply dyadic_recurrence_isBigO_nat 4
    (negativeLaplaceLogFourth F) negativeLaplaceKernelFourth 1542 (by norm_num)
  · exact ((continuousOn_id.pow 4).mul
      (continuousOn_negativeLaplaceLogFourth_Icc F hF)).abs
  · intro s hs
    norm_num
    exact negativeLaplaceLogFourth_two_mul F hF hs
  · intro s hs
    exact abs_fourth_mul_negativeLaplaceKernelFourth_le hs

end Fabius

