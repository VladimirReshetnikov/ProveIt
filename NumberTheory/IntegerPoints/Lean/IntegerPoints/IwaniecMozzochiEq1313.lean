import IntegerPoints.IwaniecMozzochiRanges
import IntegerPoints.IwaniecMozzochiSection12Blocks

/-!
# Iwaniec--Mozzochi (13.13) from the Section 14 mean-value theorem

This file isolates the elementary transfer from Theorem 14.1 to equation
(13.13).  The deep mean-value theorem remains an explicit premise.

There are two endpoint details which the paper suppresses in `1 \ll L \ll K`:

* `b2Count` uses the dyadic blocks `(K, 2K]` and `(L, 2L]`, whereas
  `meanValueCount` uses `[1, K']` and `[1, L']`.  If either original scale is
  below `1/2`, its dyadic block is empty.  Otherwise Theorem 14.1 applies at
  the enlarged scales `K' = 2K`, `L' = 2L`.
* The coefficient in (14.3) has the exact scale identity
  `sqrt K * H = X₃ * L * C`.  Hence `C <= H` gives `sqrt K <= X₃ L`, and the
  third term in (14.5) is absorbed uniformly.

Thus no lower bound such as `1 <= μ₁` is needed: the formal statement's
quantification over every `μ₁ > 0` is sound.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

private noncomputable def eq1313X (x C M : ℝ) : ℝ :=
  x ^ ((1 : ℝ) / 4) * (Ascale x C M * C) ^ (-(3 : ℝ) / 4)

/-! ## Elementary scale identities -/

private theorem eq1313_rpow_lower {x : ℝ} (hx : 0 < x) :
    x ^ ((1 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22) =
      x ^ (-(3 : ℝ) / 11) := by
  calc
    x ^ ((1 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22) =
        x ^ ((1 : ℝ) / 22 + -(7 : ℝ) / 22) :=
      (Real.rpow_add hx _ _).symm
    _ = x ^ (-(3 : ℝ) / 11) := by norm_num

/-- On the main range, the Section 10 `l`-scale does not exceed the
`k`-scale.  This is the exact-constant version of `L \ll K` used below. -/
private theorem eq1313_Lscale_le_Kscale {x C H M : ℝ}
    (hmain : InMainRange x H M) (hC : 0 ≤ C) :
    Lscale x C H M ≤ Kscale x C M := by
  rcases hmain with ⟨hx, hxM, _, hH, hHupper, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    exact mul_pos hM0 (Real.rpow_pos_of_pos hx0 _)
  have hHupper' : H ≤ M * x ^ (-(7 : ℝ) / 22) := by
    convert hHupper using 1
    norm_num [theta0]
  have hNlower : x ^ ((1 : ℝ) / 22) * H ≤ shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    calc
      x ^ ((1 : ℝ) / 22) * H ≤
          x ^ ((1 : ℝ) / 22) * (M * x ^ (-(7 : ℝ) / 22)) :=
        mul_le_mul_of_nonneg_left hHupper' (Real.rpow_nonneg hx0.le _)
      _ = M * (x ^ ((1 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22)) := by ring
      _ = M * x ^ (-(3 : ℝ) / 11) := by rw [eq1313_rpow_lower hx0]
  have hxpow : 1 ≤ x ^ ((1 : ℝ) / 22) :=
    Real.one_le_rpow hx (by norm_num)
  have hHN : H ≤ shiftLength x M := by
    calc
      H = 1 * H := by ring
      _ ≤ x ^ ((1 : ℝ) / 22) * H :=
        mul_le_mul_of_nonneg_right hxpow hH0.le
      _ ≤ shiftLength x M := hNlower
  let B : ℝ := x * C * shiftLength x M / M ^ 3
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hL : Lscale x C H M = B * H := by
    dsimp [B]
    unfold Lscale
    ring
  have hK : Kscale x C M = B * shiftLength x M := by
    dsimp [B]
    unfold Kscale
    ring
  rw [hL, hK]
  exact mul_le_mul_of_nonneg_left hHN hB0

/-- Exact identity behind the paper's
`X₃⁻¹ K⁻¹/² L⁻¹ \asymp C H⁻¹ K⁻¹`.  A logarithmic proof keeps the
quarter-powers auditable and avoids any appeal to floating-point algebra. -/
private theorem eq1313_sqrtK_mul_H {x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M)
    (hN : 0 < shiftLength x M) :
    Real.sqrt (Kscale x C M) * H =
      eq1313X x C M * Lscale x C H M * C := by
  have hA : 0 < Ascale x C M := by
    unfold Ascale
    positivity
  have hAC : 0 < Ascale x C M * C := mul_pos hA hC
  have hK : 0 < Kscale x C M := by
    unfold Kscale
    positivity
  have hL : 0 < Lscale x C H M := by
    unfold Lscale
    positivity
  have hX : 0 < eq1313X x C M := by
    unfold eq1313X
    positivity
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
      Real.log (eq1313X x C M) =
        -(1 : ℝ) / 2 * Real.log x - (3 : ℝ) / 2 * Real.log C +
          (3 : ℝ) / 2 * Real.log M := by
    unfold eq1313X
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne'
        (Real.rpow_pos_of_pos hAC _).ne',
      Real.log_rpow hx, Real.log_rpow hAC, hlogAC]
    ring
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos (Real.sqrt_pos.2 hK) hH))
    (Set.mem_Ioi.2 (mul_pos (mul_pos hX hL) hC))
  rw [Real.log_mul (Real.sqrt_pos.2 hK).ne' hH.ne', Real.log_sqrt hK.le,
    hlogK,
    Real.log_mul (mul_ne_zero hX.ne' hL.ne') hC.ne',
    Real.log_mul hX.ne' hL.ne', hlogX, hlogL]
  ring

/-! ## The dyadic block and the Section 14 count -/

private theorem dyadic_eq_empty_of_lt_half {U : ℝ} (hU : U < 1 / 2) :
    dyadic U = ∅ := by
  unfold dyadic intRange
  have h2U : 2 * U < 1 := by linarith
  rw [Nat.floor_eq_zero.2 h2U]
  simp

private theorem dyadic_subset_upTo_twice (U : ℝ) :
    dyadic U ⊆ upTo (2 * U) := by
  intro n hn
  simp only [dyadic, intRange, Finset.mem_Ioc] at hn
  simp only [upTo, Finset.mem_Icc]
  omega

/-- Dropping (13.8), every tuple counted in `b2Count` belongs to the Section
14 count at the doubled scales. -/
private theorem b2Count_le_meanValueCount {μ X K L : ℝ}
    (hX : 0 < X) (hK : 0 < K) (hL : 0 < L) :
    b2Count μ X X K L ≤
      meanValueCount (μ / (X * Real.sqrt (2 * K) * (2 * L))) (2 * K) (2 * L) := by
  unfold b2Count meanValueCount
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
  rcases hq with ⟨⟨hqK, hqL⟩, hsumL, hsumKL, hroot, _hreciprocal⟩
  refine ⟨⟨?_, ?_⟩, hsumL, hsumKL, ?_⟩
  · rw [Fintype.mem_piFinset] at hqK ⊢
    intro i
    exact dyadic_subset_upTo_twice K (hqK i)
  · rw [Fintype.mem_piFinset] at hqL ⊢
    intro i
    exact dyadic_subset_upTo_twice L (hqL i)
  · calc
      |Real.sqrt (q.1 0) * q.2 0 + Real.sqrt (q.1 1) * q.2 1 -
          Real.sqrt (q.1 2) * q.2 2 - Real.sqrt (q.1 3) * q.2 3| ≤ μ / X := hroot
      _ = (μ / (X * Real.sqrt (2 * K) * (2 * L))) *
          Real.sqrt (2 * K) * (2 * L) := by
        have hsqrt : 0 < Real.sqrt (2 * K) := Real.sqrt_pos.2 (by positivity)
        field_simp [hX.ne', hsqrt.ne', hL.ne']

/-! ## Conditional proof of (13.13) -/

/-- **Iwaniec--Mozzochi (13.13), conditionally on Theorem 14.1.**

The proof includes the dyadic endpoint cases, so it is valid for every
`μ₁ > 0` appearing in the formal statement, not merely for a hidden
`μ₁ \gg 1` regime. -/
theorem iwaniecMozzochi_eq1313_nominalBlock_of_theorem141
    (h141 : iwaniecMozzochi_theorem141) : iwaniecMozzochi_eq1313_nominalBlock := by
  intro μ₁ μ ε hμ₁ hμ hε
  obtain ⟨Cmv, hCmv⟩ := h141 ε hε
  refine ⟨|Cmv| * (2 + μ) * 4 ^ (2 + ε), ?_⟩
  intro x C H M hmain hshort hCH
  let X : ℝ := eq1313X x C M
  let K : ℝ := Kscale x C M
  let L : ℝ := Lscale x C H M
  change (b2Count μ X X K L : ℝ) ≤
    (|Cmv| * (2 + μ) * 4 ^ (2 + ε)) * (K * L) ^ (2 + ε)
  have hG := iwaniecMozzochi_eq66_holds x H M hmain
  rcases hmain with ⟨hx, hxM, hMx, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hmain' : InMainRange x H M :=
    ⟨hx, hxM, hMx, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by
    unfold shiftLength
    positivity
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hG.1
  have hC0 : 0 < C := (mul_pos hμ₁ hG0).trans hshort
  have hX0 : 0 < X := by
    dsimp [X, eq1313X]
    unfold Ascale
    positivity
  have hK0 : 0 < K := by
    dsimp [K]
    unfold Kscale
    positivity
  have hL0 : 0 < L := by
    dsimp [L]
    unfold Lscale
    positivity
  have hLK : L ≤ K := by
    dsimp [L, K]
    exact eq1313_Lscale_le_Kscale hmain' hC0.le
  have hscaleIdentity : Real.sqrt K * H = X * L * C := by
    dsimp [K, X, L]
    exact eq1313_sqrtK_mul_H hx0 hC0 hH0 hM0 hN0
  have hsqrtScale : Real.sqrt K ≤ X * L := by
    apply (mul_le_mul_iff_of_pos_right hH0).mp
    rw [hscaleIdentity]
    exact mul_le_mul_of_nonneg_left hCH (mul_nonneg hX0.le hL0.le)
  have htargetNonneg :
      0 ≤ (|Cmv| * (2 + μ) * 4 ^ (2 + ε)) * (K * L) ^ (2 + ε) := by
    positivity

  by_cases hKhalf : 1 / 2 ≤ K
  · by_cases hLhalf : 1 / 2 ≤ L
    · let δ : ℝ := μ / (X * Real.sqrt (2 * K) * (2 * L))
      have h2K : 1 ≤ 2 * K := by linarith
      have h2L : 1 ≤ 2 * L := by linarith
      have hδ0 : 0 < δ := by
        dsimp [δ]
        positivity
      have hsqrtTwo : Real.sqrt (2 : ℝ) ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_nonneg (2 : ℝ)]
      have hsqrtDouble : Real.sqrt (2 * K) ≤ X * (2 * L) := by
        calc
          Real.sqrt (2 * K) = Real.sqrt 2 * Real.sqrt K := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          _ ≤ Real.sqrt 2 * (X * L) :=
            mul_le_mul_of_nonneg_left hsqrtScale (Real.sqrt_nonneg 2)
          _ ≤ 2 * (X * L) :=
            mul_le_mul_of_nonneg_right hsqrtTwo (mul_nonneg hX0.le hL0.le)
          _ = X * (2 * L) := by ring
      have hδK : δ * (2 * K) ≤ μ := by
        have hden : 0 < X * Real.sqrt (2 * K) * (2 * L) := by positivity
        dsimp [δ]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hden).2
        have hsquare : Real.sqrt (2 * K) * Real.sqrt (2 * K) = 2 * K :=
          Real.mul_self_sqrt (by positivity)
        calc
          μ * (2 * K) = μ *
              (Real.sqrt (2 * K) * Real.sqrt (2 * K)) := by rw [hsquare]
          _ ≤ μ * (Real.sqrt (2 * K) * (X * (2 * L))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsqrtDouble (Real.sqrt_nonneg _)) hμ.le
          _ = μ * (X * Real.sqrt (2 * K) * (2 * L)) := by ring
      have hcountNat :
          b2Count μ X X K L ≤ meanValueCount δ (2 * K) (2 * L) := by
        dsimp [δ]
        exact b2Count_le_meanValueCount hX0 hK0 hL0
      have hcount :
          (b2Count μ X X K L : ℝ) ≤ (meanValueCount δ (2 * K) (2 * L) : ℝ) := by
        exact_mod_cast hcountNat
      have hmean := hCmv δ (2 * K) (2 * L) hδ0 h2K h2L
      have h2LK : 2 * L ≤ 2 * K := by linarith
      have hterm1 :
          (2 * K) * (2 * L) ^ 3 ≤ (2 * K) ^ 2 * (2 * L) ^ 2 := by
        calc
          (2 * K) * (2 * L) ^ 3 = ((2 * K) * (2 * L) ^ 2) * (2 * L) := by ring
          _ ≤ ((2 * K) * (2 * L) ^ 2) * (2 * K) :=
            mul_le_mul_of_nonneg_left h2LK (by positivity)
          _ = (2 * K) ^ 2 * (2 * L) ^ 2 := by ring
      have hterm3 :
          δ * (2 * K) ^ 3 * (2 * L) ^ 2 ≤
            μ * ((2 * K) ^ 2 * (2 * L) ^ 2) := by
        calc
          δ * (2 * K) ^ 3 * (2 * L) ^ 2 =
              (δ * (2 * K)) * ((2 * K) ^ 2 * (2 * L) ^ 2) := by ring
          _ ≤ μ * ((2 * K) ^ 2 * (2 * L) ^ 2) :=
            mul_le_mul_of_nonneg_right hδK (by positivity)
      have hpoly :
          (2 * K) * (2 * L) ^ 3 + (2 * K) ^ 2 * (2 * L) ^ 2 +
              δ * (2 * K) ^ 3 * (2 * L) ^ 2 ≤
            (2 + μ) * ((2 * K) ^ 2 * (2 * L) ^ 2) := by
        linarith
      calc
        (b2Count μ X X K L : ℝ) ≤ (meanValueCount δ (2 * K) (2 * L) : ℝ) := hcount
        _ ≤ Cmv *
            ((2 * K) * (2 * L) ^ 3 + (2 * K) ^ 2 * (2 * L) ^ 2 +
              δ * (2 * K) ^ 3 * (2 * L) ^ 2) *
                ((2 * K) * (2 * L)) ^ ε := hmean
        _ ≤ |Cmv| *
            ((2 * K) * (2 * L) ^ 3 + (2 * K) ^ 2 * (2 * L) ^ 2 +
              δ * (2 * K) ^ 3 * (2 * L) ^ 2) *
                ((2 * K) * (2 * L)) ^ ε := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self Cmv) (by positivity))
            (Real.rpow_nonneg (by positivity) _)
        _ ≤ |Cmv| * ((2 + μ) * ((2 * K) ^ 2 * (2 * L) ^ 2)) *
              ((2 * K) * (2 * L)) ^ ε := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpoly (abs_nonneg Cmv))
            (Real.rpow_nonneg (by positivity) _)
        _ = (|Cmv| * (2 + μ) * 4 ^ (2 + ε)) * (K * L) ^ (2 + ε) := by
          have hKLpos : 0 < K * L := mul_pos hK0 hL0
          have hfour : (0 : ℝ) < 4 := by norm_num
          have hsquares :
              (2 * K) ^ 2 * (2 * L) ^ 2 = 4 ^ 2 * (K * L) ^ 2 := by ring
          have hdouble : (2 * K) * (2 * L) = 4 * (K * L) := by ring
          have hfourPow : (4 : ℝ) ^ 2 * 4 ^ ε = 4 ^ (2 + ε) := by
            rw [← Real.rpow_two (4 : ℝ), ← Real.rpow_add hfour]
          have hKLPow : (K * L) ^ 2 * (K * L) ^ ε = (K * L) ^ (2 + ε) := by
            rw [← Real.rpow_two (K * L), ← Real.rpow_add hKLpos]
          calc
            |Cmv| * ((2 + μ) * ((2 * K) ^ 2 * (2 * L) ^ 2)) *
                ((2 * K) * (2 * L)) ^ ε =
                |Cmv| * (2 + μ) * ((4 : ℝ) ^ 2 * 4 ^ ε) *
                  ((K * L) ^ 2 * (K * L) ^ ε) := by
              rw [hsquares, hdouble, Real.mul_rpow hfour.le hKLpos.le]
              ring
            _ = (|Cmv| * (2 + μ) * 4 ^ (2 + ε)) * (K * L) ^ (2 + ε) := by
              rw [hfourPow, hKLPow]
    · have hLsmall : L < 1 / 2 := lt_of_not_ge hLhalf
      have hempty : dyadic L = ∅ := dyadic_eq_empty_of_lt_half hLsmall
      have hzero : b2Count μ X X K L = 0 := by simp [b2Count, hempty]
      rw [hzero]
      simpa only [Nat.cast_zero] using htargetNonneg
  · have hKsmall : K < 1 / 2 := lt_of_not_ge hKhalf
    have hempty : dyadic K = ∅ := dyadic_eq_empty_of_lt_half hKsmall
    have hzero : b2Count μ X X K L = 0 := by simp [b2Count, hempty]
    rw [hzero]
    simpa only [Nat.cast_zero] using htargetNonneg

/-- **Iwaniec--Mozzochi (13.13), uniformly over the finite Section 12 block
cover, conditionally on Theorem 14.1.**

For the block scales `Kₑ` and `Lₑ` one only has the absolute comparisons
`Lₑ ≤ 128 Kₑ` and `√(2Kₑ) ≤ 16 X (2Lₑ)`.  In Theorem 14.1 these
replace the unit comparisons used for the nominal block: the first polynomial
term costs `128`, while the third costs `16μ`.  Both losses are uniform over
`Fin 8 × Fin 9`, so the constant is chosen before the block indices. -/
theorem iwaniecMozzochi_eq1313_of_theorem141
    (h141 : iwaniecMozzochi_theorem141) : iwaniecMozzochi_eq1313 := by
  intro μ₁ μ ε hμ₁ hμ hε
  obtain ⟨Cmv, hCmv⟩ := h141 ε hε
  refine ⟨|Cmv| * (129 + 16 * μ) * 4 ^ (2 + ε), ?_⟩
  intro x C H M jK jL hmain hshort hCH
  let X : ℝ := eq1313X x C M
  let Kbase : ℝ := Kscale x C M
  let Lbase : ℝ := Lscale x C H M
  let Kb : ℝ := section12KBlockScale Kbase jK
  let Lb : ℝ := section12LBlockScale Lbase jL
  change (b2Count μ X X Kb Lb : ℝ) ≤
    (|Cmv| * (129 + 16 * μ) * 4 ^ (2 + ε)) * (Kb * Lb) ^ (2 + ε)
  have hG := iwaniecMozzochi_eq66_holds x H M hmain
  rcases hmain with ⟨hx, hxM, hMx, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hmain' : InMainRange x H M :=
    ⟨hx, hxM, hMx, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by
    unfold shiftLength
    positivity
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hG.1
  have hC0 : 0 < C := (mul_pos hμ₁ hG0).trans hshort
  have hX0 : 0 < X := by
    dsimp [X, eq1313X]
    unfold Ascale
    positivity
  have hKbase0 : 0 < Kbase := by
    dsimp [Kbase]
    unfold Kscale
    positivity
  have hLbase0 : 0 < Lbase := by
    dsimp [Lbase]
    unfold Lscale
    positivity
  have hKb0 : 0 < Kb := by
    dsimp [Kb, section12KBlockScale]
    positivity
  have hLb0 : 0 < Lb := by
    dsimp [Lb, section12LBlockScale]
    positivity
  have hLKbase : Lbase ≤ Kbase := by
    dsimp [Lbase, Kbase]
    exact eq1313_Lscale_le_Kscale hmain' hC0.le
  have hscaleIdentity : Real.sqrt Kbase * H = X * Lbase * C := by
    dsimp [Kbase, X, Lbase]
    exact eq1313_sqrtK_mul_H hx0 hC0 hH0 hM0 hN0
  have hsqrtBase : Real.sqrt Kbase ≤ X * Lbase := by
    apply (mul_le_mul_iff_of_pos_right hH0).mp
    rw [hscaleIdentity]
    exact mul_le_mul_of_nonneg_left hCH (mul_nonneg hX0.le hLbase0.le)

  have hKbLower : Kbase ≤ Kb := by
    simpa only [Kb] using section12KBlockScale_lower hKbase0.le jK
  have hKbUpper : Kb ≤ 128 * Kbase := by
    simpa only [Kb] using section12KBlockScale_upper hKbase0.le jK
  have hLbLower : Lbase / 2 ≤ Lb := by
    simpa only [Lb] using section12LBlockScale_lower hLbase0.le jL
  have hLbUpper : Lb ≤ 128 * Lbase := by
    simpa only [Lb] using section12LBlockScale_upper hLbase0.le jL
  have hLbK : Lb ≤ 128 * Kb := by
    calc
      Lb ≤ 128 * Lbase := hLbUpper
      _ ≤ 128 * Kbase :=
        mul_le_mul_of_nonneg_left hLKbase (by norm_num)
      _ ≤ 128 * Kb :=
        mul_le_mul_of_nonneg_left hKbLower (by norm_num)
  have h2LbK : 2 * Lb ≤ 128 * (2 * Kb) := by
    nlinarith
  have hLbaseTwoLb : Lbase ≤ 2 * Lb := by
    linarith
  have h2KbUpper : 2 * Kb ≤ 256 * Kbase := by
    nlinarith
  have hsqrtBlock : Real.sqrt (2 * Kb) ≤ 16 * (X * (2 * Lb)) := by
    calc
      Real.sqrt (2 * Kb) ≤ Real.sqrt (256 * Kbase) :=
        Real.sqrt_le_sqrt h2KbUpper
      _ = 16 * Real.sqrt Kbase := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 256)]
        rw [show Real.sqrt (256 : ℝ) = 16 by
          rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      _ ≤ 16 * (X * Lbase) :=
        mul_le_mul_of_nonneg_left hsqrtBase (by norm_num)
      _ ≤ 16 * (X * (2 * Lb)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hLbaseTwoLb hX0.le) (by norm_num)
  have htargetNonneg :
      0 ≤ (|Cmv| * (129 + 16 * μ) * 4 ^ (2 + ε)) *
        (Kb * Lb) ^ (2 + ε) := by
    positivity

  by_cases hKbhalf : 1 / 2 ≤ Kb
  · by_cases hLbhalf : 1 / 2 ≤ Lb
    · let δ : ℝ := μ / (X * Real.sqrt (2 * Kb) * (2 * Lb))
      have h2Kb : 1 ≤ 2 * Kb := by linarith
      have h2Lb : 1 ≤ 2 * Lb := by linarith
      have hδ0 : 0 < δ := by
        dsimp [δ]
        positivity
      have hδK : δ * (2 * Kb) ≤ 16 * μ := by
        have hden : 0 < X * Real.sqrt (2 * Kb) * (2 * Lb) := by positivity
        dsimp [δ]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hden).2
        have hsquare : Real.sqrt (2 * Kb) * Real.sqrt (2 * Kb) = 2 * Kb :=
          Real.mul_self_sqrt (by positivity)
        calc
          μ * (2 * Kb) = μ *
              (Real.sqrt (2 * Kb) * Real.sqrt (2 * Kb)) := by rw [hsquare]
          _ ≤ μ * (Real.sqrt (2 * Kb) * (16 * (X * (2 * Lb)))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsqrtBlock (Real.sqrt_nonneg _)) hμ.le
          _ = (16 * μ) * (X * Real.sqrt (2 * Kb) * (2 * Lb)) := by ring
      have hcountNat :
          b2Count μ X X Kb Lb ≤ meanValueCount δ (2 * Kb) (2 * Lb) := by
        dsimp [δ]
        exact b2Count_le_meanValueCount hX0 hKb0 hLb0
      have hcount :
          (b2Count μ X X Kb Lb : ℝ) ≤
            (meanValueCount δ (2 * Kb) (2 * Lb) : ℝ) := by
        exact_mod_cast hcountNat
      have hmean := hCmv δ (2 * Kb) (2 * Lb) hδ0 h2Kb h2Lb
      have hterm1 :
          (2 * Kb) * (2 * Lb) ^ 3 ≤
            128 * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2) := by
        calc
          (2 * Kb) * (2 * Lb) ^ 3 =
              ((2 * Kb) * (2 * Lb) ^ 2) * (2 * Lb) := by ring
          _ ≤ ((2 * Kb) * (2 * Lb) ^ 2) * (128 * (2 * Kb)) :=
            mul_le_mul_of_nonneg_left h2LbK (by positivity)
          _ = 128 * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2) := by ring
      have hterm3 :
          δ * (2 * Kb) ^ 3 * (2 * Lb) ^ 2 ≤
            (16 * μ) * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2) := by
        calc
          δ * (2 * Kb) ^ 3 * (2 * Lb) ^ 2 =
              (δ * (2 * Kb)) * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2) := by ring
          _ ≤ (16 * μ) * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2) :=
            mul_le_mul_of_nonneg_right hδK (by positivity)
      have hpoly :
          (2 * Kb) * (2 * Lb) ^ 3 + (2 * Kb) ^ 2 * (2 * Lb) ^ 2 +
              δ * (2 * Kb) ^ 3 * (2 * Lb) ^ 2 ≤
            (129 + 16 * μ) * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2) := by
        calc
          (2 * Kb) * (2 * Lb) ^ 3 + (2 * Kb) ^ 2 * (2 * Lb) ^ 2 +
                δ * (2 * Kb) ^ 3 * (2 * Lb) ^ 2 ≤
              128 * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2) +
                (2 * Kb) ^ 2 * (2 * Lb) ^ 2 +
                (16 * μ) * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2) :=
            add_le_add (add_le_add hterm1 le_rfl) hterm3
          _ = (129 + 16 * μ) * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2) := by ring
      calc
        (b2Count μ X X Kb Lb : ℝ) ≤
            (meanValueCount δ (2 * Kb) (2 * Lb) : ℝ) := hcount
        _ ≤ Cmv *
            ((2 * Kb) * (2 * Lb) ^ 3 + (2 * Kb) ^ 2 * (2 * Lb) ^ 2 +
              δ * (2 * Kb) ^ 3 * (2 * Lb) ^ 2) *
                ((2 * Kb) * (2 * Lb)) ^ ε := hmean
        _ ≤ |Cmv| *
            ((2 * Kb) * (2 * Lb) ^ 3 + (2 * Kb) ^ 2 * (2 * Lb) ^ 2 +
              δ * (2 * Kb) ^ 3 * (2 * Lb) ^ 2) *
                ((2 * Kb) * (2 * Lb)) ^ ε := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self Cmv) (by positivity))
            (Real.rpow_nonneg (by positivity) _)
        _ ≤ |Cmv| * ((129 + 16 * μ) * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2)) *
              ((2 * Kb) * (2 * Lb)) ^ ε := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpoly (abs_nonneg Cmv))
            (Real.rpow_nonneg (by positivity) _)
        _ = (|Cmv| * (129 + 16 * μ) * 4 ^ (2 + ε)) *
              (Kb * Lb) ^ (2 + ε) := by
          have hKLpos : 0 < Kb * Lb := mul_pos hKb0 hLb0
          have hfour : (0 : ℝ) < 4 := by norm_num
          have hsquares :
              (2 * Kb) ^ 2 * (2 * Lb) ^ 2 = 4 ^ 2 * (Kb * Lb) ^ 2 := by ring
          have hdouble : (2 * Kb) * (2 * Lb) = 4 * (Kb * Lb) := by ring
          have hfourPow : (4 : ℝ) ^ 2 * 4 ^ ε = 4 ^ (2 + ε) := by
            rw [← Real.rpow_two (4 : ℝ), ← Real.rpow_add hfour]
          have hKLPow : (Kb * Lb) ^ 2 * (Kb * Lb) ^ ε =
              (Kb * Lb) ^ (2 + ε) := by
            rw [← Real.rpow_two (Kb * Lb), ← Real.rpow_add hKLpos]
          calc
            |Cmv| * ((129 + 16 * μ) * ((2 * Kb) ^ 2 * (2 * Lb) ^ 2)) *
                ((2 * Kb) * (2 * Lb)) ^ ε =
                |Cmv| * (129 + 16 * μ) * ((4 : ℝ) ^ 2 * 4 ^ ε) *
                  ((Kb * Lb) ^ 2 * (Kb * Lb) ^ ε) := by
              rw [hsquares, hdouble, Real.mul_rpow hfour.le hKLpos.le]
              ring
            _ = (|Cmv| * (129 + 16 * μ) * 4 ^ (2 + ε)) *
                  (Kb * Lb) ^ (2 + ε) := by
              rw [hfourPow, hKLPow]
    · have hLbsmall : Lb < 1 / 2 := lt_of_not_ge hLbhalf
      have hempty : dyadic Lb = ∅ := dyadic_eq_empty_of_lt_half hLbsmall
      have hzero : b2Count μ X X Kb Lb = 0 := by simp [b2Count, hempty]
      rw [hzero]
      simpa only [Nat.cast_zero] using htargetNonneg
  · have hKbsmall : Kb < 1 / 2 := lt_of_not_ge hKbhalf
    have hempty : dyadic Kb = ∅ := dyadic_eq_empty_of_lt_half hKbsmall
    have hzero : b2Count μ X X Kb Lb = 0 := by simp [b2Count, hempty]
    rw [hzero]
    simpa only [Nat.cast_zero] using htargetNonneg

end LeanProofs.IntegerPoints
