import FabiusFunction.LaplaceMomentBounds
import FabiusFunction.ScalingRecurrence
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

/-- First derivative of the elementary log-product summand
`negativeLaplaceKernel x = log ((1 - exp (-x)) / x)`, in closed form.
Writing that summand as `log (1 - exp (-x)) - log x` separates the
exponential part from the rational singular part `1 / x`.  The
identification as a derivative is `negativeLaplaceKernel_hasDerivAt`, which
needs `0 < x`. -/
noncomputable def negativeLaplaceKernelFirst (x : ℝ) : ℝ :=
  Real.exp (-x) / (1 - Real.exp (-x)) - 1 / x

/-- Second derivative of `negativeLaplaceKernel`, in closed form, with the
rational singular part `1 / x ^ 2` kept as a separate summand.  The
identification is `negativeLaplaceKernelFirst_hasDerivAt`, for `0 < x`. -/
noncomputable def negativeLaplaceKernelSecond (x : ℝ) : ℝ :=
  -Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 + 1 / x ^ 2

/-- Third derivative of `negativeLaplaceKernel`, in closed form, with the
rational singular part `2 / x ^ 3` kept as a separate summand.  The
identification is `negativeLaplaceKernelSecond_hasDerivAt`, for `0 < x`. -/
noncomputable def negativeLaplaceKernelThird (x : ℝ) : ℝ :=
  Real.exp (-x) * (1 + Real.exp (-x)) /
      (1 - Real.exp (-x)) ^ 3 - 2 / x ^ 3

/-- Fourth derivative of `negativeLaplaceKernel`, in closed form, with the
rational singular part `6 / x ^ 4` kept as a separate summand.  The
identification is `negativeLaplaceKernelThird_hasDerivAt`, for `0 < x`.
This is the highest kernel derivative the module uses. -/
noncomputable def negativeLaplaceKernelFourth (x : ℝ) : ℝ :=
  -(Real.exp (-x) *
      (1 + 4 * Real.exp (-x) + Real.exp (-x) ^ 2)) /
      (1 - Real.exp (-x)) ^ 4 + 6 / x ^ 4

private lemma one_sub_exp_neg_ne {x : ℝ} (hx : 0 < x) :
    1 - Real.exp (-x) ≠ 0 := by
  apply (sub_pos.mpr ?_).ne'
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- For `0 < x` the elementary log-product summand `negativeLaplaceKernel` is
differentiable with derivative `negativeLaplaceKernelFirst x`.  This is the
kernel half of the input to `negativeLaplaceLogFirst_two_mul`, which
differentiates the exact dilation equation `negativeLaplaceLog_two_mul`. -/
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

/-- For `0 < x`, `negativeLaplaceKernelSecond x` is the derivative of
`negativeLaplaceKernelFirst`.  This is the kernel input to the
second-derivative dilation recurrence `negativeLaplaceLogSecond_two_mul`. -/
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

/-- For `0 < x`, `negativeLaplaceKernelThird x` is the derivative of
`negativeLaplaceKernelSecond`.  This is the kernel input to the
third-derivative dilation recurrence `negativeLaplaceLogThird_two_mul`. -/
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

/-- For `0 < x`, `negativeLaplaceKernelFourth x` is the derivative of
`negativeLaplaceKernelThird`.  This is the kernel input to the
fourth-derivative dilation recurrence `negativeLaplaceLogFourth_two_mul`. -/
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

private lemma exp_neg_le_half {x : ℝ} (hx : 1 ≤ x) :
    Real.exp (-x) ≤ 1 / 2 := by
  calc
    Real.exp (-x) ≤ Real.exp (-1) := by
      exact Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le

/-- On `1 ≤ x`, replacing each reciprocal factor `1 / (1 - exp (-x))` by `2`
gives a uniform bound for every natural denominator power. -/
theorem exp_neg_div_one_sub_pow_le
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

/-- Weighted kernel bound `|x * negativeLaplaceKernelFirst x| ≤ 3` on the
half-line `1 ≤ x`.  The constant is explicit but no attainment is claimed.
It is the per-step increment bound for the `j = 1` dyadic iteration behind
`negativeLaplaceLogFirst_isBigO_log_div_nat`. -/
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

/-- Weighted kernel bound `|x ^ 2 * negativeLaplaceKernelSecond x| ≤ 9` on
the half-line `1 ≤ x`.  The constant is explicit but no attainment is
claimed.  It is the per-step increment bound for the `j = 2` dyadic
iteration behind `negativeLaplaceLogSecond_isBigO_log_div_sq_nat`. -/
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

/-- Weighted kernel bound `|x ^ 3 * negativeLaplaceKernelThird x| ≤ 74` on
the half-line `1 ≤ x`.  The constant is explicit but no attainment is
claimed.  It is the per-step increment bound for the `j = 3` dyadic
iteration behind `negativeLaplaceLogThird_isBigO_log_div_cube_nat`. -/
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

/-- Weighted kernel bound `|x ^ 4 * negativeLaplaceKernelFourth x| ≤ 1542`
on the half-line `1 ≤ x`.  The constant is explicit but no attainment is
claimed.  It is the per-step increment bound for the `j = 4` dyadic
iteration behind `negativeLaplaceLogFourth_isBigO_log_div_fourth_nat`. -/
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

/-- Differentiating the exact dilation equation `negativeLaplaceLog_two_mul`
once.  The dyadic weight doubles at each order, so the first derivative
carries the weight `2`. -/
theorem negativeLaplaceLogFirst_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) :
    2 * negativeLaplaceLogFirst F (2 * s) =
      negativeLaplaceKernelFirst s + negativeLaplaceLogFirst F s :=
  hasDerivAt_of_scalingRecurrence_two_mul
    (f := negativeLaplaceLog) (f' := negativeLaplaceLogFirst F)
    (g := negativeLaplaceKernel) (g' := negativeLaplaceKernelFirst)
    (c := 1) (by norm_num)
    (fun _ ht => negativeLaplaceLog_hasDerivAt F hF ht)
    (fun _ ht => negativeLaplaceKernel_hasDerivAt ht)
    (fun t ht => (one_mul _).trans (negativeLaplaceLog_two_mul t ht)) hs

/-- The second-derivative dilation recurrence, with weight `4`. -/
theorem negativeLaplaceLogSecond_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) :
    4 * negativeLaplaceLogSecond F (2 * s) =
      negativeLaplaceKernelSecond s + negativeLaplaceLogSecond F s :=
  hasDerivAt_of_scalingRecurrence_two_mul
    (f := negativeLaplaceLogFirst F) (f' := negativeLaplaceLogSecond F)
    (g := negativeLaplaceKernelFirst) (g' := negativeLaplaceKernelSecond)
    (c := 2) (by norm_num)
    (fun _ ht => negativeLaplaceLogFirst_hasDerivAt F hF ht)
    (fun _ ht => negativeLaplaceKernelFirst_hasDerivAt ht)
    (fun _ ht => negativeLaplaceLogFirst_two_mul F hF ht) hs

/-- The third-derivative dilation recurrence, with weight `8`. -/
theorem negativeLaplaceLogThird_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) :
    8 * negativeLaplaceLogThird F (2 * s) =
      negativeLaplaceKernelThird s + negativeLaplaceLogThird F s :=
  hasDerivAt_of_scalingRecurrence_two_mul
    (f := negativeLaplaceLogSecond F) (f' := negativeLaplaceLogThird F)
    (g := negativeLaplaceKernelSecond) (g' := negativeLaplaceKernelThird)
    (c := 4) (by norm_num)
    (fun _ ht => negativeLaplaceLogSecond_hasDerivAt F hF ht)
    (fun _ ht => negativeLaplaceKernelSecond_hasDerivAt ht)
    (fun _ ht => negativeLaplaceLogSecond_two_mul F hF ht) hs

/-- The fourth-derivative dilation recurrence, with weight `16`. -/
theorem negativeLaplaceLogFourth_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) :
    16 * negativeLaplaceLogFourth F (2 * s) =
      negativeLaplaceKernelFourth s + negativeLaplaceLogFourth F s :=
  hasDerivAt_of_scalingRecurrence_two_mul
    (f := negativeLaplaceLogThird F) (f' := negativeLaplaceLogFourth F)
    (g := negativeLaplaceKernelThird) (g' := negativeLaplaceKernelFourth)
    (c := 8) (by norm_num)
    (fun _ ht => negativeLaplaceLogThird_hasDerivAt F hF ht)
    (fun _ ht => negativeLaplaceKernelThird_hasDerivAt ht)
    (fun _ ht => negativeLaplaceLogThird_two_mul F hF ht) hs

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

/-- Along the natural numbers, the first logarithmic derivative of the
negative-Laplace transform of any `F` satisfying `IsFabius` obeys
`q'(n) = O(log n / n)`.  The proof iterates the weight-`2` recurrence
`negativeLaplaceLogFirst_two_mul` outward from the compact base window
`[1, 2]`, paying `abs_mul_negativeLaplaceKernelFirst_le` at each of the
roughly `log₂ n` dyadic steps. -/
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

/-- Along the natural numbers, the second logarithmic derivative obeys
`q''(n) = O(log n / n²)`: the weight-`4` recurrence
`negativeLaplaceLogSecond_two_mul` iterated from `[1, 2]` with the increment
bound `abs_sq_mul_negativeLaplaceKernelSecond_le`.  The logarithm comes from
bounding every dyadic increment by a constant;
`negativeLaplaceLogSecond_sub_log_main_isBigO_inv_sq_nat` below instead
subtracts the exact rational main term first and so exhibits
`log n / (log 2 * n ^ 2)` explicitly with an `O(n⁻²)` remainder. -/
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

/-- Along the natural numbers, the third logarithmic derivative obeys
`q'''(n) = O(log n / n³)`: the weight-`8` recurrence
`negativeLaplaceLogThird_two_mul` iterated from `[1, 2]` with the increment
bound `abs_cube_mul_negativeLaplaceKernelThird_le`. -/
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

/-- The fourth logarithmic derivative is continuous on the compact base
window `Icc 1 2` of the dyadic iteration.  For the three lower orders this
continuity is read off a single `HasDerivAt` statement; here it is assembled
from the normalized tilted moments `R₁, …, R₄` appearing in
`negativeLaplaceLogFourth`.  It supplies the continuity hypothesis of
`negativeLaplaceLogFourth_isBigO_log_div_fourth_nat`. -/
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

/-- Along the natural numbers, the fourth logarithmic derivative obeys
`q⁽⁴⁾(n) = O(log n / n⁴)`: the weight-`16` recurrence
`negativeLaplaceLogFourth_two_mul` iterated from `[1, 2]` with the increment
bound `abs_fourth_mul_negativeLaplaceKernelFourth_le`.  This closes the
range `1 ≤ j ≤ 4` announced in the module header. -/
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

/-- After removing its rational main term, the scaled second kernel derivative
has a summable `1/x` dyadic remainder. -/
theorem abs_sq_mul_negativeLaplaceKernelSecond_sub_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    |x ^ 2 * negativeLaplaceKernelSecond x - 1| ≤ 24 / x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht0 : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
  have hden : 0 < 1 - Real.exp (-x) := by
    linarith [exp_neg_le_half hx]
  have hfrac := exp_neg_div_one_sub_pow_le 2 hx
  norm_num at hfrac
  have hpow := pow_mul_exp_neg_le_factorial 3 hx0.le
  norm_num at hpow
  unfold negativeLaplaceKernelSecond
  have heq : x ^ 2 * (-Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 +
      1 / x ^ 2) - 1 =
      -(x ^ 2 * (Real.exp (-x) / (1 - Real.exp (-x)) ^ 2)) := by
    field_simp [hx0.ne', hden.ne']
    ring
  rw [heq, abs_neg, abs_mul, abs_of_pos (pow_pos hx0 2),
    abs_of_nonneg (div_nonneg ht0 (pow_nonneg hden.le 2))]
  rw [le_div_iff₀ hx0]
  calc
    x ^ 2 * (Real.exp (-x) / (1 - Real.exp (-x)) ^ 2) * x ≤
        x ^ 2 * (4 * Real.exp (-x)) * x := by gcongr
    _ = 4 * (x ^ 3 * Real.exp (-x)) := by ring
    _ ≤ 24 := by linarith

/-- The second logarithmic derivative has the sharper asymptotic
`q''(n) = log n / (log 2 * n²) + O(n⁻²)`.  The `O(log n / n²)` estimate above
loses one logarithm because it bounds every dyadic kernel increment by a
constant.  Here the exact rational part is removed first; the remaining
increments are summable along a dyadic orbit. -/
theorem negativeLaplaceLogSecond_sub_log_main_isBigO_inv_sq_nat
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => negativeLaplaceLogSecond F n -
      Real.log (n : ℝ) / (Real.log 2 * (n : ℝ) ^ 2)) =O[atTop]
      (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  let p : ℝ → ℝ := fun s =>
    s ^ 2 * negativeLaplaceLogSecond F s - Real.log s / Real.log 2
  have hpcont : ContinuousOn (fun s => |p s|) (Icc (1 : ℝ) 2) := by
    apply ContinuousOn.abs
    apply ContinuousOn.sub
    · apply (continuousOn_id.pow 2).mul
      intro s hs
      exact (negativeLaplaceLogSecond_hasDerivAt F hF
        (zero_lt_one.trans_le hs.1)).continuousAt.continuousWithinAt
    · exact (Real.continuousOn_log.mono fun _ hs =>
        (zero_lt_one.trans_le hs.1).ne').div_const _
  obtain ⟨A₀, hA₀⟩ := bddAbove_def.mp (isCompact_Icc.bddAbove_image hpcont)
  let A : ℝ := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hbase : ∀ {s : ℝ}, 1 ≤ s → s ≤ 2 → |p s| ≤ A := by
    intro s hs1 hs2
    exact (hA₀ _ ⟨s, ⟨hs1, hs2⟩, rfl⟩).trans (le_max_left _ _)
  have hrec : ∀ {s : ℝ}, 0 < s →
      p (2 * s) = p s + (s ^ 2 * negativeLaplaceKernelSecond s - 1) := by
    intro s hs
    dsimp [p]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne']
    rw [show (2 * s) ^ 2 * negativeLaplaceLogSecond F (2 * s) =
      s ^ 2 * (4 * negativeLaplaceLogSecond F (2 * s)) by ring,
      negativeLaplaceLogSecond_two_mul F hF hs]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    ring
  have hinterval : ∀ m : ℕ, ∀ {s : ℝ}, 1 ≤ s →
      s ≤ (2 : ℝ) ^ (m + 1) → |p s| ≤ A + 48 - 48 / s := by
    intro m
    induction m with
    | zero =>
        intro s hs1 hs2
        norm_num at hs2
        calc
          |p s| ≤ A := hbase hs1 hs2
          _ ≤ A + 48 - 48 / s := by
            have : 48 / s ≤ 48 := by
              rw [div_le_iff₀ (zero_lt_one.trans_le hs1)]
              nlinarith
            linarith
    | succ m ih =>
        intro s hs1 hsupper
        by_cases hs2 : s ≤ 2
        · exact (hbase hs1 hs2).trans (by
            have : 48 / s ≤ 48 := by
              rw [div_le_iff₀ (zero_lt_one.trans_le hs1)]
              nlinarith
            linarith)
        · let t : ℝ := s / 2
          have ht1 : 1 ≤ t := by dsimp [t]; linarith
          have htupper : t ≤ (2 : ℝ) ^ (m + 1) := by
            dsimp [t]
            rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ] at hsupper
            nlinarith
          have hi := ih ht1 htupper
          have hg := abs_sq_mul_negativeLaplaceKernelSecond_sub_one_le ht1
          have hrt := hrec (show 0 < t by linarith)
          have hst : s = 2 * t := by dsimp [t]; ring
          rw [hst, hrt]
          calc
            |p t + (t ^ 2 * negativeLaplaceKernelSecond t - 1)| ≤
                |p t| + |t ^ 2 * negativeLaplaceKernelSecond t - 1| :=
              abs_add_le _ _
            _ ≤ (A + 48 - 48 / t) + 24 / t := add_le_add hi hg
            _ = A + 48 - 48 / (2 * t) := by field_simp; ring
  apply IsBigO.of_bound (A + 48)
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp := hinterval (Nat.log 2 n)
    (by exact_mod_cast hn : (1 : ℝ) ≤ n)
    (by exact_mod_cast (Nat.lt_pow_succ_log_self (by omega : 1 < 2) n).le)
  have hp' : |p n| ≤ A + 48 := hp.trans
    (sub_le_self _ (div_nonneg (by norm_num) hn0.le))
  have hA48 : 0 ≤ A + 48 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hn0))]
  change |negativeLaplaceLogSecond F n -
      Real.log (n : ℝ) / (Real.log 2 * (n : ℝ) ^ 2)| ≤
    (A + 48) * ((n : ℝ) ^ 2)⁻¹
  have heq : negativeLaplaceLogSecond F n -
      Real.log (n : ℝ) / (Real.log 2 * (n : ℝ) ^ 2) =
      p n / (n : ℝ) ^ 2 := by
    dsimp [p]
    field_simp [hn0.ne']
  rw [heq, abs_div, abs_of_pos (pow_pos hn0 2), div_eq_mul_inv]
  gcongr

end Fabius
