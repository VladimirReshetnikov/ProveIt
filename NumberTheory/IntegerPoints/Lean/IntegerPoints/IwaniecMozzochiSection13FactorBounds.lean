import IntegerPoints.IwaniecMozzochiSection13Scales
import IntegerPoints.IwaniecMozzochiSection12Blocks

/-!
# Lower bounds for the Section 13 large-sieve factors

The comparison in (13.9) replaces each factor `1 + X_j Y_j` by a constant
multiple of `X_j Y_j`.  At the nominal Section 10 scales the four lower
bounds are, with `muOne * G < C <= H`,

* `muOne < L`,
* `muOne^2 < K * L`,
* `muOne < X * sqrt K * L`, and
* `1 <= X * L / sqrt K`.

Thus the literal constant `16` is available at the nominal scales when
`1 <= muOne`.  For the formal statements, however, `muOne` is an arbitrary
positive real.  Moreover, on a finite Section 12 block only
`L / 2 <= Lb` while `Kb <= 128 K`; the fourth factor can consequently fall
below one even when its nominal value is one.  The final results below retain
the honest `muOne`-dependent constants and a fixed block loss.  They do not
require the corresponding dyadic finsets to be nonempty.
-/

open Real

namespace LeanProofs.IntegerPoints

/-! ## Exact nominal-scale identities -/

/-- The quarter-power identity underlying both of the paper's third and
fourth factor formulas. -/
theorem section13_sqrtK_mul_H_eq_X_mul_L_mul_C {x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    Real.sqrt (Kscale x C M) * H =
      section13XScale x (Ascale x C M) C * Lscale x C H M * C := by
  rcases section13_namedScales_pos hx hC hH hM with
    ⟨hN, _hG, hA, hK, hL, hX⟩
  have hAC : 0 < Ascale x C M * C := mul_pos hA hC
  have hlogA :
      Real.log (Ascale x C M) =
        Real.log x + Real.log C - 2 * Real.log M := by
    unfold Ascale
    rw [Real.log_div (mul_ne_zero hx.ne' hC.ne') (pow_ne_zero 2 hM.ne'),
      Real.log_mul hx.ne' hC.ne', Real.log_pow]
    ring
  have hlogAC :
      Real.log (Ascale x C M * C) =
        Real.log x + 2 * Real.log C - 2 * Real.log M := by
    rw [Real.log_mul hA.ne' hC.ne', hlogA]
    ring
  have hlogK :
      Real.log (Kscale x C M) =
        Real.log x + Real.log C + 2 * Real.log (shiftLength x M) -
          3 * Real.log M := by
    unfold Kscale
    rw [Real.log_div
        (mul_ne_zero (mul_ne_zero hx.ne' hC.ne') (pow_ne_zero 2 hN.ne'))
        (pow_ne_zero 3 hM.ne'),
      Real.log_mul (mul_ne_zero hx.ne' hC.ne') (pow_ne_zero 2 hN.ne'),
      Real.log_mul hx.ne' hC.ne', Real.log_pow, Real.log_pow]
    ring
  have hlogL :
      Real.log (Lscale x C H M) =
        Real.log x + Real.log C + Real.log H + Real.log (shiftLength x M) -
          3 * Real.log M := by
    unfold Lscale
    rw [Real.log_div
        (mul_ne_zero
          (mul_ne_zero (mul_ne_zero hx.ne' hC.ne') hH.ne') hN.ne')
        (pow_ne_zero 3 hM.ne'),
      Real.log_mul (mul_ne_zero (mul_ne_zero hx.ne' hC.ne') hH.ne') hN.ne',
      Real.log_mul (mul_ne_zero hx.ne' hC.ne') hH.ne',
      Real.log_mul hx.ne' hC.ne', Real.log_pow]
    ring
  have hlogX :
      Real.log (section13XScale x (Ascale x C M) C) =
        -(1 : ℝ) / 2 * Real.log x - (3 : ℝ) / 2 * Real.log C +
          (3 : ℝ) / 2 * Real.log M := by
    unfold section13XScale
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne'
        (Real.rpow_pos_of_pos hAC _).ne',
      Real.log_rpow hx, Real.log_rpow hAC, hlogAC]
    ring
  apply Real.log_injOn_pos
    (Set.mem_Ioi.2 (mul_pos (Real.sqrt_pos.2 hK) hH))
    (Set.mem_Ioi.2 (mul_pos (mul_pos hX hL) hC))
  rw [Real.log_mul (Real.sqrt_pos.2 hK).ne' hH.ne', Real.log_sqrt hK.le,
    hlogK,
    Real.log_mul (mul_ne_zero hX.ne' hL.ne') hC.ne',
    Real.log_mul hX.ne' hL.ne', hlogX, hlogL]
  ring

/-- The paper's exact fourth-factor identity
`X * L / sqrt K = H / C` at the nominal Section 10 scales. -/
theorem section13_fourth_factor_eq {x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    section13XScale x (Ascale x C M) C * Lscale x C H M /
        Real.sqrt (Kscale x C M) =
      H / C := by
  have hK : 0 < Kscale x C M := by
    unfold Kscale shiftLength
    positivity
  have hsqrt : 0 < Real.sqrt (Kscale x C M) := Real.sqrt_pos.2 hK
  rw [div_eq_div_iff hsqrt.ne' hC.ne']
  calc
    (section13XScale x (Ascale x C M) C * Lscale x C H M) * C =
        Real.sqrt (Kscale x C M) * H :=
      (section13_sqrtK_mul_H_eq_X_mul_L_mul_C hx hC hH hM).symm
    _ = H * Real.sqrt (Kscale x C M) := by ring

/-- The paper's exact third-factor identity
`X * sqrt K * L = x * H * N^2 / M^3` at the nominal Section 10 scales. -/
theorem section13_third_factor_eq {x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    section13XScale x (Ascale x C M) C * Real.sqrt (Kscale x C M) *
        Lscale x C H M =
      x * H * shiftLength x M ^ 2 / M ^ 3 := by
  have hK : 0 < Kscale x C M := by
    unfold Kscale shiftLength
    positivity
  have hsqrt : 0 < Real.sqrt (Kscale x C M) := Real.sqrt_pos.2 hK
  have hsquare :
      Real.sqrt (Kscale x C M) * Real.sqrt (Kscale x C M) =
        Kscale x C M := Real.mul_self_sqrt hK.le
  calc
    section13XScale x (Ascale x C M) C * Real.sqrt (Kscale x C M) *
          Lscale x C H M =
        (Real.sqrt (Kscale x C M) * Real.sqrt (Kscale x C M)) *
          (section13XScale x (Ascale x C M) C * Lscale x C H M) /
            Real.sqrt (Kscale x C M) := by
      field_simp [hsqrt.ne']
    _ = Kscale x C M *
          (section13XScale x (Ascale x C M) C * Lscale x C H M /
            Real.sqrt (Kscale x C M)) := by
      rw [hsquare]
      ring
    _ = Kscale x C M * (H / C) := by
      rw [section13_fourth_factor_eq hx hC hH hM]
    _ = x * H * shiftLength x M ^ 2 / M ^ 3 := by
      unfold Kscale
      field_simp [hC.ne', hM.ne']

/-! ## Main-range lower bounds at the nominal scales -/

/-- The shift length is at least `H` throughout `InMainRange`. -/
theorem section13_H_le_shiftLength_of_mainRange {x H M : ℝ}
    (hmain : InMainRange x H M) :
    H ≤ shiftLength x M := by
  rcases hmain with ⟨hx, hxM, _, _, hHupper, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hHupper' : H ≤ M * x ^ (-(7 : ℝ) / 22) := by
    convert hHupper using 1
    norm_num [theta0]
  have hpow : x ^ (-(7 : ℝ) / 22) ≤ x ^ (-(3 : ℝ) / 11) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  rw [shiftLength_eq_mul_rpow]
  exact hHupper'.trans (mul_le_mul_of_nonneg_left hpow hM0.le)

/-- Consequently the nominal `L` scale is no larger than the nominal `K`
scale. -/
theorem section13_Lscale_le_Kscale_of_mainRange {x C H M : ℝ}
    (hmain : InMainRange x H M) (hC : 0 ≤ C) :
    Lscale x C H M ≤ Kscale x C M := by
  rcases hmain with ⟨hx, hxM, hMx, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hmain' : InMainRange x H M :=
    ⟨hx, hxM, hMx, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hN0 : 0 < shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    positivity
  have hL0 : 0 ≤ Lscale x C H M := by
    unfold Lscale
    positivity
  have hHN : H ≤ shiftLength x M :=
    section13_H_le_shiftLength_of_mainRange hmain'
  apply (mul_le_mul_iff_of_pos_right hH0).mp
  rw [section13_Kscale_mul_H]
  exact mul_le_mul_of_nonneg_left hHN hL0

/-- The short-denominator condition alone gives the precise lower bound
`muOne < L`; positivity of `muOne` is not needed for this implication. -/
theorem section13_muOne_lt_Lscale {muOne x C H M : ℝ}
    (hmain : InMainRange x H M)
    (hshort : muOne * Gscale x H M < C) :
    muOne < Lscale x C H M := by
  have hG := iwaniecMozzochi_eq66_holds x H M hmain
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hG.1
  rcases hmain with ⟨hx, hxM, _, hH, _, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  apply (mul_lt_mul_iff_of_pos_right hG0).mp
  calc
    muOne * Gscale x H M < C := hshort
    _ = Lscale x C H M * Gscale x H M :=
      (section13_Lscale_mul_Gscale hx0 hH0 hM0).symm

/-- All four honest nominal lower bounds.  The first three retain the
dependence on the arbitrary positive parameter `muOne`; only the fourth is
bounded below by one independently of it. -/
theorem section13_nominal_factor_lower_bounds {muOne x C H M : ℝ}
    (hmuOne : 0 < muOne) (hmain : InMainRange x H M)
    (hshort : muOne * Gscale x H M < C) (hCH : C ≤ H) :
    muOne < Lscale x C H M ∧
      muOne ^ 2 < Kscale x C M * Lscale x C H M ∧
      muOne < section13XScale x (Ascale x C M) C *
        Real.sqrt (Kscale x C M) * Lscale x C H M ∧
      1 ≤ section13XScale x (Ascale x C M) C * Lscale x C H M /
        Real.sqrt (Kscale x C M) := by
  have hG := iwaniecMozzochi_eq66_holds x H M hmain
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hG.1
  have hC0 : 0 < C := (mul_pos hmuOne hG0).trans hshort
  rcases hmain with ⟨hx, hxM, hMx, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hmain' : InMainRange x H M :=
    ⟨hx, hxM, hMx, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  rcases section13_namedScales_pos hx0 hC0 hH0 hM0 with
    ⟨hN0, _hGnamed, _hA0, hK0, hL0, _hX0⟩
  have hLmu : muOne < Lscale x C H M :=
    section13_muOne_lt_Lscale hmain' hshort
  have hLK : Lscale x C H M ≤ Kscale x C M :=
    section13_Lscale_le_Kscale_of_mainRange hmain' hC0.le
  have hKmu : muOne < Kscale x C M := hLmu.trans_le hLK
  have hKLmu : muOne ^ 2 < Kscale x C M * Lscale x C H M := by
    calc
      muOne ^ 2 = muOne * muOne := by ring
      _ < Lscale x C H M * muOne :=
        mul_lt_mul_of_pos_right hLmu hmuOne
      _ < Lscale x C H M * Lscale x C H M :=
        mul_lt_mul_of_pos_left hLmu hL0
      _ ≤ Kscale x C M * Lscale x C H M :=
        mul_le_mul_of_nonneg_right hLK hL0.le
  have hfourth :
      1 ≤ section13XScale x (Ascale x C M) C * Lscale x C H M /
        Real.sqrt (Kscale x C M) := by
    rw [section13_fourth_factor_eq hx0 hC0 hH0 hM0]
    exact (le_div_iff₀ hC0).2 (by simpa using hCH)
  let B : ℝ := x * shiftLength x M ^ 2 / M ^ 3
  have hB0 : 0 < B := by
    dsimp [B]
    positivity
  have hKform : Kscale x C M = B * C := by
    dsimp [B]
    unfold Kscale
    ring
  have hthirdForm :
      section13XScale x (Ascale x C M) C * Real.sqrt (Kscale x C M) *
          Lscale x C H M = B * H := by
    rw [section13_third_factor_eq hx0 hC0 hH0 hM0]
    dsimp [B]
    ring
  have hthird :
      muOne < section13XScale x (Ascale x C M) C *
        Real.sqrt (Kscale x C M) * Lscale x C H M := by
    calc
      muOne < Kscale x C M := hKmu
      _ = B * C := hKform
      _ ≤ B * H := mul_le_mul_of_nonneg_left hCH hB0.le
      _ = section13XScale x (Ascale x C M) C *
          Real.sqrt (Kscale x C M) * Lscale x C H M := hthirdForm.symm
  exact ⟨hLmu, hKLmu, hthird, hfourth⟩

/-- The literal factor-`16` comparison is valid at the nominal scales once
the customary analytic convention `1 <= muOne` is made explicit. -/
theorem section13_nominal_largeSieveProduct_le_sixteen {muOne x C H M : ℝ}
    (hmuOne : 1 ≤ muOne) (hmain : InMainRange x H M)
    (hshort : muOne * Gscale x H M < C) (hCH : C ≤ H) :
    section13LargeSieveProduct x (Ascale x C M) C (Kscale x C M)
        (Lscale x C H M) ≤
      16 * (x ^ ((1 : ℝ) / 2) * (Ascale x C M * C) ^ (-(3 : ℝ) / 2) *
        Kscale x C M * Lscale x C H M ^ 4) := by
  have hmuOne0 : 0 < muOne := zero_lt_one.trans_le hmuOne
  rcases section13_nominal_factor_lower_bounds hmuOne0 hmain hshort hCH with
    ⟨hL, hKL, hthird, hfourth⟩
  have hG := iwaniecMozzochi_eq66_holds x H M hmain
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hG.1
  have hC0 : 0 < C := (mul_pos hmuOne0 hG0).trans hshort
  rcases section13_namedScales_pos_of_mainRange hmain hC0 with
    ⟨_hN, _hGnamed, hA, hK, _hL, _hX⟩
  apply section13LargeSieveProduct_le_sixteen
    (zero_lt_one.trans_le hmain.1) hA hC0 hK
  · exact hmuOne.trans hL.le
  · exact (one_le_pow₀ hmuOne).trans hKL.le
  · exact hmuOne.trans hthird.le
  · exact hfourth

/-! ## Transport to the finite Section 12 blocks -/

/-- Uniform lower bounds on every one of the 72 finite block scales.  No
nonemptiness premise on either dyadic block is used.  The loss `1 / 32` in the
fourth factor is a convenient rational consequence of `Kb <= 128 K` and
`L / 2 <= Lb`; the sharp endpoint loss is `1 / (16 * sqrt 2)`. -/
theorem section13_block_factor_lower_bounds {muOne x C H M : ℝ}
    (jK : Fin 8) (jL : Fin 9)
    (hmuOne : 0 < muOne) (hmain : InMainRange x H M)
    (hshort : muOne * Gscale x H M < C) (hCH : C ≤ H) :
    muOne / 2 < section12LBlockScale (Lscale x C H M) jL ∧
      muOne ^ 2 / 2 <
        section12KBlockScale (Kscale x C M) jK *
          section12LBlockScale (Lscale x C H M) jL ∧
      muOne / 2 <
        section13XScale x (Ascale x C M) C *
          Real.sqrt (section12KBlockScale (Kscale x C M) jK) *
          section12LBlockScale (Lscale x C H M) jL ∧
      1 / 32 ≤
        section13XScale x (Ascale x C M) C *
          section12LBlockScale (Lscale x C H M) jL /
          Real.sqrt (section12KBlockScale (Kscale x C M) jK) := by
  have hG := iwaniecMozzochi_eq66_holds x H M hmain
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hG.1
  have hC0 : 0 < C := (mul_pos hmuOne hG0).trans hshort
  rcases section13_namedScales_pos_of_mainRange hmain hC0 with
    ⟨_hN, _hGnamed, _hA, hK, hL, hX⟩
  let Kb : ℝ := section12KBlockScale (Kscale x C M) jK
  let Lb : ℝ := section12LBlockScale (Lscale x C H M) jL
  have hKb : 0 < Kb := by
    dsimp [Kb, section12KBlockScale]
    positivity
  have hLb : 0 < Lb := by
    dsimp [Lb, section12LBlockScale]
    positivity
  have hKbLower : Kscale x C M ≤ Kb := by
    simpa only [Kb] using section12KBlockScale_lower hK.le jK
  have hKbUpper : Kb ≤ 128 * Kscale x C M := by
    simpa only [Kb] using section12KBlockScale_upper hK.le jK
  have hLbLower : Lscale x C H M / 2 ≤ Lb := by
    simpa only [Lb] using section12LBlockScale_lower hL.le jL
  rcases section13_nominal_factor_lower_bounds hmuOne hmain hshort hCH with
    ⟨hLmu, hKLmu, hthirdMu, hfourth⟩
  have hfirstBlock : muOne / 2 < Lb :=
    (div_lt_div_of_pos_right hLmu (by norm_num)).trans_le hLbLower
  have hproductLower :
      Kscale x C M * Lscale x C H M / 2 ≤ Kb * Lb := by
    calc
      Kscale x C M * Lscale x C H M / 2 =
          Kscale x C M * (Lscale x C H M / 2) := by ring
      _ ≤ Kscale x C M * Lb :=
        mul_le_mul_of_nonneg_left hLbLower hK.le
      _ ≤ Kb * Lb := mul_le_mul_of_nonneg_right hKbLower hLb.le
  have hsecondBlock : muOne ^ 2 / 2 < Kb * Lb :=
    (div_lt_div_of_pos_right hKLmu (by norm_num)).trans_le hproductLower
  have hsqrtLower : Real.sqrt (Kscale x C M) ≤ Real.sqrt Kb :=
    Real.sqrt_le_sqrt hKbLower
  have hthirdLower :
      (section13XScale x (Ascale x C M) C * Real.sqrt (Kscale x C M) *
          Lscale x C H M) / 2 ≤
        section13XScale x (Ascale x C M) C * Real.sqrt Kb * Lb := by
    calc
      (section13XScale x (Ascale x C M) C * Real.sqrt (Kscale x C M) *
            Lscale x C H M) / 2 =
          (section13XScale x (Ascale x C M) C *
            Real.sqrt (Kscale x C M)) * (Lscale x C H M / 2) := by ring
      _ ≤ (section13XScale x (Ascale x C M) C *
            Real.sqrt (Kscale x C M)) * Lb :=
        mul_le_mul_of_nonneg_left hLbLower
          (mul_nonneg hX.le (Real.sqrt_nonneg _))
      _ ≤ section13XScale x (Ascale x C M) C * Real.sqrt Kb * Lb :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrtLower hX.le) hLb.le
  have hthirdBlock :
      muOne / 2 < section13XScale x (Ascale x C M) C * Real.sqrt Kb * Lb :=
    (div_lt_div_of_pos_right hthirdMu (by norm_num)).trans_le hthirdLower
  have hsqrtK : 0 < Real.sqrt (Kscale x C M) := Real.sqrt_pos.2 hK
  have hsqrtKb : 0 < Real.sqrt Kb := Real.sqrt_pos.2 hKb
  have hsqrt128 : Real.sqrt (128 : ℝ) ≤ 16 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 128),
      Real.sqrt_nonneg (128 : ℝ)]
  have hsqrtUpper : Real.sqrt Kb ≤ 16 * Real.sqrt (Kscale x C M) := by
    calc
      Real.sqrt Kb ≤ Real.sqrt (128 * Kscale x C M) :=
        Real.sqrt_le_sqrt hKbUpper
      _ = Real.sqrt 128 * Real.sqrt (Kscale x C M) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 128)]
      _ ≤ 16 * Real.sqrt (Kscale x C M) :=
        mul_le_mul_of_nonneg_right hsqrt128 (Real.sqrt_nonneg _)
  have hinvSqrt :
      1 / (16 * Real.sqrt (Kscale x C M)) ≤ 1 / Real.sqrt Kb :=
    one_div_le_one_div_of_le hsqrtKb hsqrtUpper
  have hdenStep :
      (section13XScale x (Ascale x C M) C * (Lscale x C H M / 2)) /
          (16 * Real.sqrt (Kscale x C M)) ≤
        (section13XScale x (Ascale x C M) C * (Lscale x C H M / 2)) /
          Real.sqrt Kb := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hinvSqrt
        (mul_nonneg hX.le (div_nonneg hL.le (by norm_num)))
  have hnumStep :
      (section13XScale x (Ascale x C M) C * (Lscale x C H M / 2)) /
          Real.sqrt Kb ≤
        section13XScale x (Ascale x C M) C * Lb / Real.sqrt Kb := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLbLower hX.le) hsqrtKb.le
  have hrescale :
      (section13XScale x (Ascale x C M) C * Lscale x C H M /
          Real.sqrt (Kscale x C M)) / 32 =
        (section13XScale x (Ascale x C M) C * (Lscale x C H M / 2)) /
          (16 * Real.sqrt (Kscale x C M)) := by
    field_simp [hsqrtK.ne']
    ring
  have hfourthBlock :
      1 / 32 ≤ section13XScale x (Ascale x C M) C * Lb / Real.sqrt Kb := by
    calc
      1 / 32 ≤
          (section13XScale x (Ascale x C M) C * Lscale x C H M /
            Real.sqrt (Kscale x C M)) / 32 :=
        div_le_div_of_nonneg_right hfourth (by norm_num)
      _ = (section13XScale x (Ascale x C M) C * (Lscale x C H M / 2)) /
          (16 * Real.sqrt (Kscale x C M)) := hrescale
      _ ≤ (section13XScale x (Ascale x C M) C * (Lscale x C H M / 2)) /
          Real.sqrt Kb := hdenStep
      _ ≤ section13XScale x (Ascale x C M) C * Lb / Real.sqrt Kb := hnumStep
  simpa only [Kb, Lb] using
    ⟨hfirstBlock, hsecondBlock, hthirdBlock, hfourthBlock⟩

/-! ## Constant-sensitive replacement for the factor-`16` argument -/

private theorem one_add_le_lower_scaled {c t : ℝ}
    (hc : 0 < c) (hct : c ≤ t) :
    1 + t ≤ (1 + 1 / c) * t := by
  have hone : 1 ≤ t / c := (le_div_iff₀ hc).2 (by simpa using hct)
  calc
    1 + t ≤ t / c + t := by
      simpa only [add_comm] using add_le_add_right hone t
    _ = (1 + 1 / c) * t := by
      field_simp [hc.ne']
      ring

/-- A constant-sensitive version of
`section13LargeSieveProduct_le_sixteen`.  It is applicable when the four
factors merely have specified positive lower bounds. -/
theorem section13LargeSieveProduct_le_of_lowerBounds
    {x A C K L c₁ c₂ c₃ c₄ : ℝ}
    (hx : 0 < x) (hA : 0 < A) (hC : 0 < C) (hK : 0 < K)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄)
    (h₁ : c₁ ≤ L) (h₂ : c₂ ≤ K * L)
    (h₃ : c₃ ≤ section13XScale x A C * Real.sqrt K * L)
    (h₄ : c₄ ≤ section13XScale x A C * L / Real.sqrt K) :
    section13LargeSieveProduct x A C K L ≤
      ((1 + 1 / c₁) * (1 + 1 / c₂) * (1 + 1 / c₃) * (1 + 1 / c₄)) *
        (x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4) := by
  have ht₁ : 0 < L := hc₁.trans_le h₁
  have ht₂ : 0 < K * L := hc₂.trans_le h₂
  have ht₃ : 0 < section13XScale x A C * Real.sqrt K * L := hc₃.trans_le h₃
  have ht₄ : 0 < section13XScale x A C * L / Real.sqrt K := hc₄.trans_le h₄
  have hu₁ : 0 < (1 + 1 / c₁) * L :=
    mul_pos (add_pos zero_lt_one (div_pos zero_lt_one hc₁)) ht₁
  have hu₂ : 0 < (1 + 1 / c₂) * (K * L) :=
    mul_pos (add_pos zero_lt_one (div_pos zero_lt_one hc₂)) ht₂
  have hu₃ : 0 <
      (1 + 1 / c₃) * (section13XScale x A C * Real.sqrt K * L) :=
    mul_pos (add_pos zero_lt_one (div_pos zero_lt_one hc₃)) ht₃
  have hb₁ : 1 + L ≤ (1 + 1 / c₁) * L :=
    one_add_le_lower_scaled hc₁ h₁
  have hb₂ : 1 + K * L ≤ (1 + 1 / c₂) * (K * L) :=
    one_add_le_lower_scaled hc₂ h₂
  have hb₃ : 1 + section13XScale x A C * Real.sqrt K * L ≤
      (1 + 1 / c₃) * (section13XScale x A C * Real.sqrt K * L) :=
    one_add_le_lower_scaled hc₃ h₃
  have hb₄ : 1 + section13XScale x A C * L / Real.sqrt K ≤
      (1 + 1 / c₄) * (section13XScale x A C * L / Real.sqrt K) :=
    one_add_le_lower_scaled hc₄ h₄
  have h₁₂ :
      (1 + L) * (1 + K * L) ≤
        ((1 + 1 / c₁) * L) * ((1 + 1 / c₂) * (K * L)) :=
    mul_le_mul hb₁ hb₂ (add_pos zero_lt_one ht₂).le hu₁.le
  have h₁₂₃ :
      (1 + L) * (1 + K * L) *
          (1 + section13XScale x A C * Real.sqrt K * L) ≤
        ((1 + 1 / c₁) * L) * ((1 + 1 / c₂) * (K * L)) *
          ((1 + 1 / c₃) * (section13XScale x A C * Real.sqrt K * L)) :=
    mul_le_mul h₁₂ hb₃ (add_pos zero_lt_one ht₃).le
      (mul_pos hu₁ hu₂).le
  have h₁₂₃₄ :
      (1 + L) * (1 + K * L) *
          (1 + section13XScale x A C * Real.sqrt K * L) *
          (1 + section13XScale x A C * L / Real.sqrt K) ≤
        ((1 + 1 / c₁) * L) * ((1 + 1 / c₂) * (K * L)) *
          ((1 + 1 / c₃) * (section13XScale x A C * Real.sqrt K * L)) *
          ((1 + 1 / c₄) * (section13XScale x A C * L / Real.sqrt K)) :=
    mul_le_mul h₁₂₃ hb₄ (add_pos zero_lt_one ht₄).le
      (mul_pos (mul_pos hu₁ hu₂) hu₃).le
  calc
    section13LargeSieveProduct x A C K L =
        (1 + L) * (1 + K * L) *
          (1 + section13XScale x A C * Real.sqrt K * L) *
          (1 + section13XScale x A C * L / Real.sqrt K) := rfl
    _ ≤ ((1 + 1 / c₁) * L) * ((1 + 1 / c₂) * (K * L)) *
          ((1 + 1 / c₃) * (section13XScale x A C * Real.sqrt K * L)) *
          ((1 + 1 / c₄) * (section13XScale x A C * L / Real.sqrt K)) :=
      h₁₂₃₄
    _ = ((1 + 1 / c₁) * (1 + 1 / c₂) * (1 + 1 / c₃) * (1 + 1 / c₄)) *
          (L * (K * L) *
            (section13XScale x A C * Real.sqrt K * L) *
            (section13XScale x A C * L / Real.sqrt K)) := by ring
    _ = ((1 + 1 / c₁) * (1 + 1 / c₂) * (1 + 1 / c₃) * (1 + 1 / c₄)) *
        (x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4) := by
      rw [section13LargeSieveMonomial_eq hx hA hC hK]

/-- For arbitrary `muOne > 0`, the nominal product comparison has an explicit
`muOne`-dependent constant. -/
theorem section13_nominal_largeSieveProduct_le_muOne {muOne x C H M : ℝ}
    (hmuOne : 0 < muOne) (hmain : InMainRange x H M)
    (hshort : muOne * Gscale x H M < C) (hCH : C ≤ H) :
    section13LargeSieveProduct x (Ascale x C M) C (Kscale x C M)
        (Lscale x C H M) ≤
      (2 * (1 + 1 / muOne) ^ 2 * (1 + 1 / muOne ^ 2)) *
        (x ^ ((1 : ℝ) / 2) * (Ascale x C M * C) ^ (-(3 : ℝ) / 2) *
          Kscale x C M * Lscale x C H M ^ 4) := by
  rcases section13_nominal_factor_lower_bounds hmuOne hmain hshort hCH with
    ⟨hL, hKL, hthird, hfourth⟩
  have hG := iwaniecMozzochi_eq66_holds x H M hmain
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hG.1
  have hC0 : 0 < C := (mul_pos hmuOne hG0).trans hshort
  rcases section13_namedScales_pos_of_mainRange hmain hC0 with
    ⟨_hN, _hGnamed, hA, hK, _hL, _hX⟩
  calc
    section13LargeSieveProduct x (Ascale x C M) C (Kscale x C M)
        (Lscale x C H M) ≤
      ((1 + 1 / muOne) * (1 + 1 / muOne ^ 2) *
          (1 + 1 / muOne) * (1 + 1 / 1)) *
        (x ^ ((1 : ℝ) / 2) * (Ascale x C M * C) ^ (-(3 : ℝ) / 2) *
          Kscale x C M * Lscale x C H M ^ 4) :=
      section13LargeSieveProduct_le_of_lowerBounds
        (zero_lt_one.trans_le hmain.1) hA hC0 hK
        hmuOne (pow_pos hmuOne 2) hmuOne zero_lt_one
        hL.le hKL.le hthird.le hfourth
    _ = (2 * (1 + 1 / muOne) ^ 2 * (1 + 1 / muOne ^ 2)) *
        (x ^ ((1 : ℝ) / 2) * (Ascale x C M * C) ^ (-(3 : ℝ) / 2) *
          Kscale x C M * Lscale x C H M ^ 4) := by ring

/-- Every finite Section 12 block admits a uniform product comparison.  The
constant depends on `muOne`, as the formal quantifiers require, and includes
the fixed loss from the fourth block factor. -/
theorem section13_block_largeSieveProduct_le_muOne {muOne x C H M : ℝ}
    (jK : Fin 8) (jL : Fin 9)
    (hmuOne : 0 < muOne) (hmain : InMainRange x H M)
    (hshort : muOne * Gscale x H M < C) (hCH : C ≤ H) :
    section13LargeSieveProduct x (Ascale x C M) C
        (section12KBlockScale (Kscale x C M) jK)
        (section12LBlockScale (Lscale x C H M) jL) ≤
      (33 * (1 + 2 / muOne) ^ 2 * (1 + 2 / muOne ^ 2)) *
        (x ^ ((1 : ℝ) / 2) * (Ascale x C M * C) ^ (-(3 : ℝ) / 2) *
          section12KBlockScale (Kscale x C M) jK *
          section12LBlockScale (Lscale x C H M) jL ^ 4) := by
  rcases section13_block_factor_lower_bounds jK jL hmuOne hmain hshort hCH with
    ⟨hL, hKL, hthird, hfourth⟩
  have hG := iwaniecMozzochi_eq66_holds x H M hmain
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hG.1
  have hC0 : 0 < C := (mul_pos hmuOne hG0).trans hshort
  rcases section13_namedScales_pos_of_mainRange hmain hC0 with
    ⟨_hN, _hGnamed, hA, hK, hLbase, _hX⟩
  have hKb : 0 < section12KBlockScale (Kscale x C M) jK := by
    unfold section12KBlockScale
    positivity
  have hcoeff :
      (1 + 1 / (muOne / 2)) * (1 + 1 / (muOne ^ 2 / 2)) *
          (1 + 1 / (muOne / 2)) * (1 + 1 / (1 / 32)) =
        33 * (1 + 2 / muOne) ^ 2 * (1 + 2 / muOne ^ 2) := by
    field_simp [hmuOne.ne']
    ring
  calc
    section13LargeSieveProduct x (Ascale x C M) C
        (section12KBlockScale (Kscale x C M) jK)
        (section12LBlockScale (Lscale x C H M) jL) ≤
      ((1 + 1 / (muOne / 2)) * (1 + 1 / (muOne ^ 2 / 2)) *
          (1 + 1 / (muOne / 2)) * (1 + 1 / (1 / 32))) *
        (x ^ ((1 : ℝ) / 2) * (Ascale x C M * C) ^ (-(3 : ℝ) / 2) *
          section12KBlockScale (Kscale x C M) jK *
          section12LBlockScale (Lscale x C H M) jL ^ 4) :=
      section13LargeSieveProduct_le_of_lowerBounds
        (zero_lt_one.trans_le hmain.1) hA hC0 hKb
        (div_pos hmuOne (by norm_num))
        (div_pos (pow_pos hmuOne 2) (by norm_num))
        (div_pos hmuOne (by norm_num)) (by norm_num)
        hL.le hKL.le hthird.le hfourth
    _ = (33 * (1 + 2 / muOne) ^ 2 * (1 + 2 / muOne ^ 2)) *
        (x ^ ((1 : ℝ) / 2) * (Ascale x C M * C) ^ (-(3 : ℝ) / 2) *
          section12KBlockScale (Kscale x C M) jK *
          section12LBlockScale (Lscale x C H M) jL ^ 4) := by
      rw [hcoeff]

end LeanProofs.IntegerPoints
