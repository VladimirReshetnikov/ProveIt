import IntegerPoints.IwaniecMozzochiEq84

/-!
# Explicit Section 8 remainder bounds for Iwaniec--Mozzochi (8.4)

This module supplies the quantitative real-window estimates quoted immediately
before (8.4).  The exact factorizations already proved in
`IwaniecMozzochiEq84` are bounded on the whole interval `0 <= u <= 8N`, not
only at natural summation points.  This is the interval needed when the mean
value theorem is applied between consecutive active indices.

The estimates are deliberately generous and completely explicit:

* `|t(u)| <= 30000 * x * H * N^3 / M^4`;
* `|t'(u)| <= 30000 * x * H * N^2 / M^4`.

Only the elementary scale data used in the paper enter the generic lemmas:
`M / 2 <= m`, `m <= 2M`, `M <= m + v`, `0 <= v <= N`,
`0 <= u <= 8N`, and `1 <= N <= M`.  The final theorem derives all of these
facts from `InMainRange`, `InFareySet`, and the Fourier shell condition.
-/

open Real Set

namespace LeanProofs.IntegerPoints

open IMReductionEq75

noncomputable section

/-! ## Elementary real-window estimates -/

/-- The two denominators in the factored formulas for `t` and `t'` are
uniformly bounded below by `M^5 / 4` throughout the real half-window
`0 <= u`.  These are exactly the denominator facts needed below. -/
theorem section8_real_window_denominator_bounds
    {M m v u : Real} (hM : 0 < M) (hmLower : M / 2 <= m)
    (hmvLower : M <= m + v) (hu : 0 <= u) :
    0 < m ∧ 0 < m + u ∧ 0 < m + v ∧
      M ^ 5 / 4 <= m * (m + u) * (m + v) ^ 3 ∧
      M ^ 5 / 4 <= (m + u) ^ 2 * (m + v) ^ 3 := by
  have hhalfM : 0 < M / 2 := by positivity
  have hm : 0 < m := hhalfM.trans_le hmLower
  have hmuLower : M / 2 <= m + u := by linarith
  have hmu : 0 < m + u := hhalfM.trans_le hmuLower
  have hmv : 0 < m + v := hM.trans_le hmvLower
  have hmvCube : M ^ 3 <= (m + v) ^ 3 :=
    pow_le_pow_left₀ hM.le hmvLower 3
  have hmmu : (M / 2) * (M / 2) <= m * (m + u) :=
    mul_le_mul hmLower hmuLower hhalfM.le hm.le
  have hfirst : M ^ 5 / 4 <= m * (m + u) * (m + v) ^ 3 := by
    calc
      M ^ 5 / 4 = (M / 2) * (M / 2) * M ^ 3 := by ring
      _ <= m * (m + u) * (m + v) ^ 3 :=
        mul_le_mul hmmu hmvCube (by positivity) (mul_nonneg hm.le hmu.le)
  have hmuSq : (M / 2) ^ 2 <= (m + u) ^ 2 :=
    pow_le_pow_left₀ hhalfM.le hmuLower 2
  have hsecond : M ^ 5 / 4 <= (m + u) ^ 2 * (m + v) ^ 3 := by
    calc
      M ^ 5 / 4 = (M / 2) ^ 2 * M ^ 3 := by ring
      _ <= (m + u) ^ 2 * (m + v) ^ 3 :=
        mul_le_mul hmuSq hmvCube (by positivity) (sq_nonneg (m + u))
  exact ⟨hm, hmu, hmv, hfirst, hsecond⟩

/-- The cubic polynomial in the exact factorization of `t` is at most
`200 * M * N^2` in absolute value on the full real window. -/
private theorem section8_remainderPolynomial_abs_le
    {M N m v u : Real} (hM : 0 <= M) (hN : 0 <= N) (hNM : N <= M)
    (hm : 0 <= m) (hmUpper : m <= 2 * M)
    (hv : 0 <= v) (hvN : v <= N)
    (hu : 0 <= u) (huUpper : u <= 8 * N) :
    |m * u ^ 2 - 3 * m * u * v + 3 * m * v ^ 2 + v ^ 3| <=
      200 * M * N ^ 2 := by
  have huSq : u ^ 2 <= 64 * N ^ 2 := by
    calc
      u ^ 2 <= (8 * N) ^ 2 := (sq_le_sq₀ hu (by positivity)).2 huUpper
      _ = 64 * N ^ 2 := by ring
  have hvSq : v ^ 2 <= N ^ 2 :=
    (sq_le_sq₀ hv hN).2 hvN
  have huv : u * v <= 8 * N ^ 2 := by
    calc
      u * v <= (8 * N) * N :=
        mul_le_mul huUpper hvN hv (by positivity)
      _ = 8 * N ^ 2 := by ring
  have hA : m * u ^ 2 <= 128 * M * N ^ 2 := by
    calc
      m * u ^ 2 <= (2 * M) * (64 * N ^ 2) :=
        mul_le_mul hmUpper huSq (sq_nonneg u) (by positivity)
      _ = 128 * M * N ^ 2 := by ring
  have hBbase : m * u * v <= 16 * M * N ^ 2 := by
    calc
      m * u * v = m * (u * v) := by ring
      _ <= (2 * M) * (8 * N ^ 2) :=
        mul_le_mul hmUpper huv (mul_nonneg hu hv) (by positivity)
      _ = 16 * M * N ^ 2 := by ring
  have hB : 3 * m * u * v <= 48 * M * N ^ 2 := by
    calc
      3 * m * u * v = 3 * (m * u * v) := by ring
      _ <= 3 * (16 * M * N ^ 2) :=
        mul_le_mul_of_nonneg_left hBbase (by norm_num)
      _ = 48 * M * N ^ 2 := by ring
  have hCbase : m * v ^ 2 <= 2 * M * N ^ 2 :=
    mul_le_mul hmUpper hvSq (sq_nonneg v) (by positivity)
  have hC : 3 * m * v ^ 2 <= 6 * M * N ^ 2 := by
    calc
      3 * m * v ^ 2 = 3 * (m * v ^ 2) := by ring
      _ <= 3 * (2 * M * N ^ 2) :=
        mul_le_mul_of_nonneg_left hCbase (by norm_num)
      _ = 6 * M * N ^ 2 := by ring
  have hvCube : v ^ 3 <= M * N ^ 2 := by
    calc
      v ^ 3 = v * v ^ 2 := by ring
      _ <= N * N ^ 2 :=
        mul_le_mul hvN hvSq (sq_nonneg v) hN
      _ <= M * N ^ 2 :=
        mul_le_mul_of_nonneg_right hNM (sq_nonneg N)
  have hA0 : 0 <= m * u ^ 2 := by positivity
  have hB0 : 0 <= 3 * m * u * v := by positivity
  have hC0 : 0 <= 3 * m * v ^ 2 := by positivity
  have hD0 : 0 <= v ^ 3 := by positivity
  have hscale : 0 <= M * N ^ 2 := mul_nonneg hM (sq_nonneg N)
  calc
    |m * u ^ 2 - 3 * m * u * v + 3 * m * v ^ 2 + v ^ 3| <=
        |m * u ^ 2 - 3 * m * u * v + 3 * m * v ^ 2| + |v ^ 3| :=
      abs_add_le _ _
    _ <= (|m * u ^ 2 - 3 * m * u * v| + |3 * m * v ^ 2|) +
        |v ^ 3| := by
      have htriangle :=
        abs_add_le (m * u ^ 2 - 3 * m * u * v) (3 * m * v ^ 2)
      linarith
    _ <= ((|m * u ^ 2| + |3 * m * u * v|) + |3 * m * v ^ 2|) +
        |v ^ 3| := by
      have htriangle := abs_sub (m * u ^ 2) (3 * m * u * v)
      linarith
    _ = m * u ^ 2 + 3 * m * u * v + 3 * m * v ^ 2 + v ^ 3 := by
      rw [abs_of_nonneg hA0, abs_of_nonneg hB0,
        abs_of_nonneg hC0, abs_of_nonneg hD0]
    _ <= 200 * M * N ^ 2 := by
      nlinarith [hscale]

/-- The two variable factors in the exact derivative numerator have the
uniform bounds used in the paper's `t'` estimate. -/
private theorem section8_remainderDerivative_factors
    {M N m v u : Real} (hM : 0 <= M) (hN : 0 <= N) (hNM : N <= M)
    (hm : 0 <= m) (hmUpper : m <= 2 * M)
    (hv : 0 <= v) (hvN : v <= N)
    (hu : 0 <= u) (huUpper : u <= 8 * N) :
    (u - v) ^ 2 <= 81 * N ^ 2 ∧
      0 <= 3 * m + 2 * u + v ∧
      3 * m + 2 * u + v <= 23 * M := by
  have hdiffAbs : |u - v| <= 9 * N := by
    rw [abs_le]
    constructor <;> nlinarith
  have hdiffSq : (u - v) ^ 2 <= 81 * N ^ 2 := by
    calc
      (u - v) ^ 2 = |u - v| ^ 2 := (sq_abs (u - v)).symm
      _ <= (9 * N) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hdiffAbs 2
      _ = 81 * N ^ 2 := by ring
  have hlinear0 : 0 <= 3 * m + 2 * u + v := by positivity
  have hlinear : 3 * m + 2 * u + v <= 23 * M := by
    nlinarith
  exact ⟨hdiffSq, hlinear0, hlinear⟩

/-! ## Generic explicit remainder bounds -/

/-- Explicit bound for the exact Section 8 remainder on a real window. -/
theorem section8Remainder_abs_le_of_window
    {x h H M N m v u : Real}
    (hx : 0 <= x) (hh : 0 <= h) (hhUpper : h <= 4 * H)
    (hH : 0 <= H) (hM : 0 < M) (hN : 0 <= N) (hNM : N <= M)
    (hmLower : M / 2 <= m) (hmUpper : m <= 2 * M)
    (hv : 0 <= v) (hvN : v <= N)
    (hu : 0 <= u) (huUpper : u <= 8 * N)
    (hmvLower : M <= m + v) :
    |section8Remainder x h m v u| <=
      30000 * x * H * N ^ 3 / M ^ 4 := by
  obtain ⟨hm, hmu, hmv, hdenLower, _hderivDenLower⟩ :=
    section8_real_window_denominator_bounds hM hmLower hmvLower hu
  have hpoly := section8_remainderPolynomial_abs_le hM.le hN hNM hm.le hmUpper
    hv hvN hu huUpper
  have hxh : x * h <= 4 * x * H := by
    calc
      x * h <= x * (4 * H) := mul_le_mul_of_nonneg_left hhUpper hx
      _ = 4 * x * H := by ring
  have hxhu : x * h * u <= 32 * x * H * N := by
    calc
      x * h * u <= (4 * x * H) * (8 * N) :=
        mul_le_mul hxh huUpper hu (by positivity)
      _ = 32 * x * H * N := by ring
  have hnumCore :
      x * h * u *
          |m * u ^ 2 - 3 * m * u * v + 3 * m * v ^ 2 + v ^ 3| <=
        6400 * x * H * M * N ^ 3 := by
    calc
      x * h * u *
          |m * u ^ 2 - 3 * m * u * v + 3 * m * v ^ 2 + v ^ 3| <=
          (32 * x * H * N) * (200 * M * N ^ 2) :=
        mul_le_mul hxhu hpoly (abs_nonneg _) (by positivity)
      _ = 6400 * x * H * M * N ^ 3 := by ring
  have hnum :
      |x * h * u *
          (m * u ^ 2 - 3 * m * u * v + 3 * m * v ^ 2 + v ^ 3)| <=
        7500 * x * H * M * N ^ 3 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hx,
      abs_of_nonneg hh, abs_of_nonneg hu]
    calc
      x * h * u *
          |m * u ^ 2 - 3 * m * u * v + 3 * m * v ^ 2 + v ^ 3| <=
          6400 * x * H * M * N ^ 3 := hnumCore
      _ <= 7500 * x * H * M * N ^ 3 := by
        have hscale : 0 <= x * H * M * N ^ 3 := by positivity
        calc
          6400 * x * H * M * N ^ 3 =
              6400 * (x * H * M * N ^ 3) := by ring
          _ <= 7500 * (x * H * M * N ^ 3) :=
            mul_le_mul_of_nonneg_right (by norm_num) hscale
          _ = 7500 * x * H * M * N ^ 3 := by ring
  have hdenPos : 0 < m * (m + u) * (m + v) ^ 3 := by positivity
  rw [section8Remainder_eq_factored hm.ne' hmv.ne' hmu.ne',
    abs_div, abs_neg, abs_of_pos hdenPos]
  calc
    |x * h * u *
        (m * u ^ 2 - 3 * m * u * v + 3 * m * v ^ 2 + v ^ 3)| /
          (m * (m + u) * (m + v) ^ 3) <=
        (7500 * x * H * M * N ^ 3) / (M ^ 5 / 4) :=
      div_le_div₀ (by positivity) hnum (by positivity) hdenLower
    _ = 30000 * x * H * N ^ 3 / M ^ 4 := by
      field_simp [hM.ne'] <;> ring

/-- Explicit bound for the exact derivative of the Section 8 remainder on a
real window. -/
theorem section8RemainderDeriv_abs_le_of_window
    {x h H M N m v u : Real}
    (hx : 0 <= x) (hh : 0 <= h) (hhUpper : h <= 4 * H)
    (hH : 0 <= H) (hM : 0 < M) (hN : 0 <= N) (hNM : N <= M)
    (hmLower : M / 2 <= m) (hmUpper : m <= 2 * M)
    (hv : 0 <= v) (hvN : v <= N)
    (hu : 0 <= u) (huUpper : u <= 8 * N)
    (hmvLower : M <= m + v) :
    |section8RemainderDeriv x h m v u| <=
      30000 * x * H * N ^ 2 / M ^ 4 := by
  obtain ⟨_hm, hmu, hmv, _hdenLower, hderivDenLower⟩ :=
    section8_real_window_denominator_bounds hM hmLower hmvLower hu
  have hm : 0 <= m := (le_trans (by positivity : 0 <= M / 2) hmLower)
  obtain ⟨hdiffSq, hlinear0, hlinear⟩ :=
    section8_remainderDerivative_factors hM.le hN hNM hm hmUpper
      hv hvN hu huUpper
  have hxh : x * h <= 4 * x * H := by
    calc
      x * h <= x * (4 * H) := mul_le_mul_of_nonneg_left hhUpper hx
      _ = 4 * x * H := by ring
  have hxhdiff : x * h * (u - v) ^ 2 <= 324 * x * H * N ^ 2 := by
    calc
      x * h * (u - v) ^ 2 <= (4 * x * H) * (81 * N ^ 2) :=
        mul_le_mul hxh hdiffSq (sq_nonneg _) (by positivity)
      _ = 324 * x * H * N ^ 2 := by ring
  have hnumCore :
      x * h * (u - v) ^ 2 * (3 * m + 2 * u + v) <=
        7452 * x * H * M * N ^ 2 := by
    calc
      x * h * (u - v) ^ 2 * (3 * m + 2 * u + v) <=
          (324 * x * H * N ^ 2) * (23 * M) :=
        mul_le_mul hxhdiff hlinear hlinear0 (by positivity)
      _ = 7452 * x * H * M * N ^ 2 := by ring
  have hnum :
      |x * h * (u - v) ^ 2 * (3 * m + 2 * u + v)| <=
        7500 * x * H * M * N ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hx,
      abs_of_nonneg hh, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg hlinear0]
    calc
      x * h * (u - v) ^ 2 * (3 * m + 2 * u + v) <=
          7452 * x * H * M * N ^ 2 := hnumCore
      _ <= 7500 * x * H * M * N ^ 2 := by
        have hscale : 0 <= x * H * M * N ^ 2 := by positivity
        calc
          7452 * x * H * M * N ^ 2 =
              7452 * (x * H * M * N ^ 2) := by ring
          _ <= 7500 * (x * H * M * N ^ 2) :=
            mul_le_mul_of_nonneg_right (by norm_num) hscale
          _ = 7500 * x * H * M * N ^ 2 := by ring
  have hdenPos : 0 < (m + u) ^ 2 * (m + v) ^ 3 := by positivity
  rw [section8RemainderDeriv_eq_factored hmv.ne' hmu.ne',
    abs_div, abs_neg, abs_of_pos hdenPos]
  calc
    |x * h * (u - v) ^ 2 * (3 * m + 2 * u + v)| /
          ((m + u) ^ 2 * (m + v) ^ 3) <=
        (7500 * x * H * M * N ^ 2) / (M ^ 5 / 4) :=
      div_le_div₀ (by positivity) hnum (by positivity) hderivDenLower
    _ = 30000 * x * H * N ^ 2 / M ^ 4 := by
      field_simp [hM.ne'] <;> ring

/-! ## Farey specialization on the full scaled support window -/

/-- All scale inequalities required by the generic bounds hold uniformly at
every real `u` in `[0, 8 * shiftLength x M]`. -/
theorem section8_farey_real_window_geometry
    {x H M u : Real} {a c : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hu : u ∈ Set.Icc (0 : Real) (8 * shiftLength x M)) :
    0 < x ∧ 0 < H ∧ 0 < M ∧
      1 <= shiftLength x M ∧ shiftLength x M <= M ∧
      M / 2 <= (fareyPoint x a c : Real) ∧
      0 <= fareyFrac x a c ∧ fareyFrac x a c < 1 ∧
      fareyFrac x a c <= shiftLength x M ∧
      (fareyPoint x a c : Real) <= 2 * M ∧
      M <= (fareyPoint x a c : Real) + fareyFrac x a c ∧
      (fareyPoint x a c : Real) + fareyFrac x a c <= 2 * M ∧
      0 <= u ∧ u <= 8 * shiftLength x M := by
  have hmain' : InMainRange x H M := hmain
  rcases hmain with
    ⟨hx, hxM, _hMx, hH, _hHupper, _hHlower, _hHlowerTwo, _hMlower⟩
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  have hMPos : 0 < M := (Real.rpow_pos_of_pos hxPos theta0).trans hxM
  have hNOne := one_le_section8_shiftLength hmain'
  have hNM := section8_shiftLength_le_M hmain'
  rcases fareyPoint_geometry hmain' hfarey with
    ⟨_hmNat, hv, hvOne, hsum, _hcoefficient, hsumLower, hsumUpper⟩
  have hmvLower : M <= (fareyPoint x a c : Real) + fareyFrac x a c := by
    rw [hsum]
    exact hsumLower
  have hmvUpper : (fareyPoint x a c : Real) + fareyFrac x a c <= 2 * M := by
    rw [hsum]
    exact hsumUpper
  have hmUpper : (fareyPoint x a c : Real) <= 2 * M := by
    linarith
  have hvN : fareyFrac x a c <= shiftLength x M :=
    hvOne.le.trans hNOne
  exact ⟨hxPos, hHPos, hMPos, hNOne, hNM,
    half_M_le_fareyPoint hmain' hfarey, hv, hvOne, hvN, hmUpper,
    hmvLower, hmvUpper, hu.1, hu.2⟩

/-- The named formula `section8RemainderDeriv` really is the derivative at
every real point of the scaled support window.  This pole-free specialization
is the form needed for a mean-value-theorem argument between two active
indices. -/
theorem section8_farey_remainder_hasDerivAt
    {x H M u : Real} {a c h : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hu : u ∈ Set.Icc (0 : Real) (8 * shiftLength x M)) :
    HasDerivAt
      (section8Remainder x h (fareyPoint x a c) (fareyFrac x a c))
      (section8RemainderDeriv x h (fareyPoint x a c) (fareyFrac x a c) u) u := by
  rcases fareyPoint_geometry hmain hfarey with
    ⟨hm, _hv, _hvOne, _hsum, _hcoefficient, _hmLower, _hmUpper⟩
  have hmPos : 0 < (fareyPoint x a c : Real) := by exact_mod_cast hm
  apply section8Remainder_hasDerivAt
  exact (add_pos_of_pos_of_nonneg hmPos hu.1).ne'

/-- The paper's `t(u)` estimate, uniformly on the entire real scaled window
needed for consecutive-index interpolation. -/
theorem section8_farey_remainder_abs_le
    {x H M u : Real} {a c h : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H))
    (hu : u ∈ Set.Icc (0 : Real) (8 * shiftLength x M)) :
    |section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) u| <=
      30000 * x * H * (shiftLength x M) ^ 3 / M ^ 4 := by
  rcases section8_farey_real_window_geometry hmain hfarey hu with
    ⟨hx, hH, hM, _hNOne, hNM, hmLower, hv, _hvOne, hvN, hmUpper,
      hmvLower, _hmvUpper, hu0, huUpper⟩
  exact section8Remainder_abs_le_of_window hx.le (Nat.cast_nonneg h)
    (mem_intRange_four_mul hH hh).2 hH.le hM
    (section8_shiftLength_pos hmain).le hNM hmLower hmUpper hv hvN
    hu0 huUpper hmvLower

/-- The paper's `t'(u)` estimate, uniformly on the entire real scaled window
needed for consecutive-index interpolation. -/
theorem section8_farey_remainderDeriv_abs_le
    {x H M u : Real} {a c h : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H))
    (hu : u ∈ Set.Icc (0 : Real) (8 * shiftLength x M)) :
    |section8RemainderDeriv x h (fareyPoint x a c) (fareyFrac x a c) u| <=
      30000 * x * H * (shiftLength x M) ^ 2 / M ^ 4 := by
  rcases section8_farey_real_window_geometry hmain hfarey hu with
    ⟨hx, hH, hM, _hNOne, hNM, hmLower, hv, _hvOne, hvN, hmUpper,
      hmvLower, _hmvUpper, hu0, huUpper⟩
  exact section8RemainderDeriv_abs_le_of_window hx.le (Nat.cast_nonneg h)
    (mem_intRange_four_mul hH hh).2 hH.le hM
    (section8_shiftLength_pos hmain).le hNM hmLower hmUpper hv hvN
    hu0 huUpper hmvLower

/-- The two explicit estimates packaged together for downstream partial
summation. -/
theorem section8_farey_remainder_window_bounds
    {x H M u : Real} {a c h : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H))
    (hu : u ∈ Set.Icc (0 : Real) (8 * shiftLength x M)) :
    |section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) u| <=
        30000 * x * H * (shiftLength x M) ^ 3 / M ^ 4 ∧
      |section8RemainderDeriv x h (fareyPoint x a c) (fareyFrac x a c) u| <=
        30000 * x * H * (shiftLength x M) ^ 2 / M ^ 4 :=
  ⟨section8_farey_remainder_abs_le hmain hfarey hh hu,
    section8_farey_remainderDeriv_abs_le hmain hfarey hh hu⟩

end

end LeanProofs.IntegerPoints
