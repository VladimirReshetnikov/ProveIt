import IntegerPoints.IwaniecMozzochiRanges

/-!
# Elementary Section 13 scales in Iwaniec--Mozzochi

This file records the scale algebra used in Section 13 independently of the
Hölder and double-large-sieve estimates.  In particular,
`section13LargeSieveProduct` is the literal product in (13.9), not an asserted
upper bound for it.  The comparison with its monomial requires lower bounds
for all four factors `X_j Y_j`; an exact hypothesis-level version is proved
below.

At the named scales `A`, `G`, `K`, `L`, and `N = shiftLength x M`, the final
monomial in the paper simplifies exactly to

`(M / N) * (C / H)^3 * x`.

Only positivity and elementary real-power algebra enter these results.
-/

open Real

namespace LeanProofs.IntegerPoints

/-! ## The four-dimensional large-sieve scales -/

/-- The common third and fourth spacing scale in Section 13:
`X₃ = X₄ = x^(1/4) (A C)^(-3/4)`. -/
noncomputable def section13XScale (x A C : ℝ) : ℝ :=
  x ^ ((1 : ℝ) / 4) * (A * C) ^ (-(3 : ℝ) / 4)

/-- The literal product `∏_{j=1}^4 (1 + X_j Y_j)` from (13.9), with
`X₁ = X₂ = 1`, `X₃ = X₄ = section13XScale x A C`, and
`Y₁ = L`, `Y₂ = K L`, `Y₃ = sqrt K L`, `Y₄ = L / sqrt K`.

This definition deliberately does not build in the paper's comparison
`1 + X_j Y_j ≪ X_j Y_j`; that comparison needs separate positive lower
bounds for the four products. -/
noncomputable def section13LargeSieveProduct (x A C K L : ℝ) : ℝ :=
  let X := section13XScale x A C
  (1 + L) * (1 + K * L) * (1 + X * Real.sqrt K * L) *
    (1 + X * L / Real.sqrt K)

/-- The Section 13 spacing scale is positive when its three input scales are
positive. -/
theorem section13XScale_pos {x A C : ℝ}
    (hx : 0 < x) (hA : 0 < A) (hC : 0 < C) :
    0 < section13XScale x A C := by
  unfold section13XScale
  exact mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos (mul_pos hA hC) _)

/-- The literal large-sieve product is positive on positive `x,A,C,K` and
nonnegative `L`. -/
theorem section13LargeSieveProduct_pos {x A C K L : ℝ}
    (hx : 0 < x) (hA : 0 < A) (hC : 0 < C) (hK : 0 < K) (hL : 0 ≤ L) :
    0 < section13LargeSieveProduct x A C K L := by
  have hX : 0 < section13XScale x A C := section13XScale_pos hx hA hC
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have h₁ : 0 < 1 + L := add_pos_of_pos_of_nonneg zero_lt_one hL
  have h₂ : 0 < 1 + K * L :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hK.le hL)
  have h₃ : 0 < 1 + section13XScale x A C * Real.sqrt K * L :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg hX.le hsqrt.le) hL)
  have h₄ : 0 < 1 + section13XScale x A C * L / Real.sqrt K :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (mul_nonneg hX.le hL) hsqrt.le)
  simpa only [section13LargeSieveProduct] using
    (mul_pos (mul_pos (mul_pos h₁ h₂) h₃) h₄)

/-- Squaring `X₃ = X₄` gives the monomial occurring on the right of (13.9). -/
theorem section13XScale_sq {x A C : ℝ}
    (hx : 0 < x) (hA : 0 < A) (hC : 0 < C) :
    section13XScale x A C ^ 2 =
      x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) := by
  have hAC : 0 < A * C := mul_pos hA hC
  have hxpow : (x ^ ((1 : ℝ) / 4)) ^ 2 = x ^ ((1 : ℝ) / 2) := by
    calc
      (x ^ ((1 : ℝ) / 4)) ^ 2 =
          x ^ (((1 : ℝ) / 4) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hx.le _ 2).symm
      _ = x ^ ((1 : ℝ) / 2) := by congr 1 <;> norm_num
  have hACpow : ((A * C) ^ (-(3 : ℝ) / 4)) ^ 2 =
      (A * C) ^ (-(3 : ℝ) / 2) := by
    calc
      ((A * C) ^ (-(3 : ℝ) / 4)) ^ 2 =
          (A * C) ^ ((-(3 : ℝ) / 4) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hAC.le _ 2).symm
      _ = (A * C) ^ (-(3 : ℝ) / 2) := by congr 1 <;> norm_num
  unfold section13XScale
  rw [mul_pow, hxpow, hACpow]

/-- The exact product of the four `X_j Y_j` in (13.9). -/
theorem section13LargeSieveMonomial_eq {x A C K L : ℝ}
    (hx : 0 < x) (hA : 0 < A) (hC : 0 < C) (hK : 0 < K) :
    L * (K * L) *
          (section13XScale x A C * Real.sqrt K * L) *
          (section13XScale x A C * L / Real.sqrt K) =
      x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4 := by
  have hsqrt : Real.sqrt K ≠ 0 := (Real.sqrt_pos.2 hK).ne'
  calc
    L * (K * L) *
          (section13XScale x A C * Real.sqrt K * L) *
          (section13XScale x A C * L / Real.sqrt K) =
        section13XScale x A C ^ 2 * K * L ^ 4 *
          (Real.sqrt K / Real.sqrt K) := by ring
    _ = section13XScale x A C ^ 2 * K * L ^ 4 := by
      rw [div_self hsqrt, mul_one]
    _ = x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4 := by
      rw [section13XScale_sq hx hA hC]

/-- Exact constant version of the elementary implication used in (13.9): if
each `X_j Y_j` is at least one, then the literal product is at most sixteen
times their monomial product.  The analytic work is precisely to establish
these four lower bounds (up to fixed constants) in the range at hand. -/
theorem section13LargeSieveProduct_le_sixteen {x A C K L : ℝ}
    (hx : 0 < x) (hA : 0 < A) (hC : 0 < C) (hK : 0 < K)
    (h₁ : 1 ≤ L) (h₂ : 1 ≤ K * L)
    (h₃ : 1 ≤ section13XScale x A C * Real.sqrt K * L)
    (h₄ : 1 ≤ section13XScale x A C * L / Real.sqrt K) :
    section13LargeSieveProduct x A C K L ≤
      16 * (x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4) := by
  have hL0 : 0 ≤ L := zero_le_one.trans h₁
  have hKL0 : 0 ≤ K * L := zero_le_one.trans h₂
  have hXsqrtKL0 : 0 ≤ section13XScale x A C * Real.sqrt K * L :=
    zero_le_one.trans h₃
  have hXLsqrtK0 : 0 ≤ section13XScale x A C * L / Real.sqrt K :=
    zero_le_one.trans h₄
  have hb₁ : 1 + L ≤ 2 * L := by linarith
  have hb₂ : 1 + K * L ≤ 2 * (K * L) := by linarith
  have hb₃ : 1 + section13XScale x A C * Real.sqrt K * L ≤
      2 * (section13XScale x A C * Real.sqrt K * L) := by linarith
  have hb₄ : 1 + section13XScale x A C * L / Real.sqrt K ≤
      2 * (section13XScale x A C * L / Real.sqrt K) := by linarith
  have h₁₂ : (1 + L) * (1 + K * L) ≤ (2 * L) * (2 * (K * L)) :=
    mul_le_mul hb₁ hb₂ (by positivity) (by positivity)
  have h₁₂₃ : (1 + L) * (1 + K * L) *
      (1 + section13XScale x A C * Real.sqrt K * L) ≤
      (2 * L) * (2 * (K * L)) *
        (2 * (section13XScale x A C * Real.sqrt K * L)) :=
    mul_le_mul h₁₂ hb₃ (by positivity) (by positivity)
  have h₁₂₃₄ : (1 + L) * (1 + K * L) *
        (1 + section13XScale x A C * Real.sqrt K * L) *
        (1 + section13XScale x A C * L / Real.sqrt K) ≤
      (2 * L) * (2 * (K * L)) *
        (2 * (section13XScale x A C * Real.sqrt K * L)) *
        (2 * (section13XScale x A C * L / Real.sqrt K)) :=
    mul_le_mul h₁₂₃ hb₄ (by positivity) (by positivity)
  calc
    section13LargeSieveProduct x A C K L =
        (1 + L) * (1 + K * L) *
          (1 + section13XScale x A C * Real.sqrt K * L) *
          (1 + section13XScale x A C * L / Real.sqrt K) := rfl
    _ ≤ (2 * L) * (2 * (K * L)) *
          (2 * (section13XScale x A C * Real.sqrt K * L)) *
          (2 * (section13XScale x A C * L / Real.sqrt K)) := h₁₂₃₄
    _ = 16 * (L * (K * L) *
          (section13XScale x A C * Real.sqrt K * L) *
          (section13XScale x A C * L / Real.sqrt K)) := by ring
    _ = 16 * (x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4) := by
      rw [section13LargeSieveMonomial_eq hx hA hC hK]

/-! ## Named-scale identities -/

/-- All Section 13 named scales, including `X₃ = X₄`, are positive whenever
`x,C,H,M` are positive. -/
theorem section13_namedScales_pos {x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    0 < shiftLength x M ∧
      0 < Gscale x H M ∧
      0 < Ascale x C M ∧
      0 < Kscale x C M ∧
      0 < Lscale x C H M ∧
      0 < section13XScale x (Ascale x C M) C := by
  have hN : 0 < shiftLength x M := by
    unfold shiftLength
    exact mul_pos hM (Real.rpow_pos_of_pos hx _)
  have hG : 0 < Gscale x H M := by
    unfold Gscale
    exact div_pos (pow_pos hM 3) (mul_pos (mul_pos hx hN) hH)
  have hA : 0 < Ascale x C M := by
    unfold Ascale
    exact div_pos (mul_pos hx hC) (pow_pos hM 2)
  have hK : 0 < Kscale x C M := by
    unfold Kscale
    exact div_pos (mul_pos (mul_pos hx hC) (pow_pos hN 2)) (pow_pos hM 3)
  have hL : 0 < Lscale x C H M := by
    unfold Lscale
    exact div_pos (mul_pos (mul_pos (mul_pos hx hC) hH) hN) (pow_pos hM 3)
  exact ⟨hN, hG, hA, hK, hL, section13XScale_pos hx hA hC⟩

/-- Main-range wrapper for positivity of all named Section 13 scales. -/
theorem section13_namedScales_pos_of_mainRange {x C H M : ℝ}
    (hmain : InMainRange x H M) (hC : 0 < C) :
    0 < shiftLength x M ∧
      0 < Gscale x H M ∧
      0 < Ascale x C M ∧
      0 < Kscale x C M ∧
      0 < Lscale x C H M ∧
      0 < section13XScale x (Ascale x C M) C := by
  rcases hmain with ⟨hx, hxM, _, hH, _, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  exact section13_namedScales_pos hx0 hC hH0 hM0

/-- The elementary identity `A C = x C² / M²`. -/
theorem section13_Ascale_mul_C (x C M : ℝ) :
    Ascale x C M * C = x * C ^ 2 / M ^ 2 := by
  unfold Ascale
  ring

/-- A denominator-free form of `K/L = N/H`, valid without positivity
assumptions. -/
theorem section13_Kscale_mul_H (x C H M : ℝ) :
    Kscale x C M * H = Lscale x C H M * shiftLength x M := by
  unfold Kscale Lscale
  ring

/-- The exact Section 10 relation `L G = C`. -/
theorem section13_Lscale_mul_Gscale {x C H M : ℝ}
    (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) :
    Lscale x C H M * Gscale x H M = C := by
  have hN : 0 < shiftLength x M := by
    unfold shiftLength
    exact mul_pos hM (Real.rpow_pos_of_pos hx _)
  unfold Lscale Gscale
  field_simp [hx.ne', hN.ne', hH.ne', hM.ne']

/-- The three half-power factors in the Section 13 final monomial collapse to
an ordinary reciprocal.  This isolates all nonintegral-power algebra used in
the core scale identity below. -/
theorem section13_halfPowerProduct_eq {x C M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hM : 0 < M) :
    Ascale x C M ^ ((3 : ℝ) / 2) * C ^ (-(7 : ℝ) / 2) *
        x ^ (-(3 : ℝ) / 2) =
      (C ^ 2 * M ^ 3)⁻¹ := by
  have hA : 0 < Ascale x C M := by
    unfold Ascale
    exact div_pos (mul_pos hx hC) (pow_pos hM 2)
  have hA32 : 0 < Ascale x C M ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hA _
  have hCneg : 0 < C ^ (-(7 : ℝ) / 2) := Real.rpow_pos_of_pos hC _
  have hxneg : 0 < x ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hx _
  have hden : 0 < C ^ 2 * M ^ 3 := mul_pos (pow_pos hC 2) (pow_pos hM 3)
  have hlogA :
      Real.log (Ascale x C M) =
        Real.log x + Real.log C - 2 * Real.log M := by
    unfold Ascale
    rw [Real.log_div (mul_ne_zero hx.ne' hC.ne') (pow_ne_zero 2 hM.ne'),
      Real.log_mul hx.ne' hC.ne', Real.log_pow]
    ring
  apply Real.log_injOn_pos
    (Set.mem_Ioi.2 (mul_pos (mul_pos hA32 hCneg) hxneg))
    (Set.mem_Ioi.2 (inv_pos.2 hden))
  rw [Real.log_mul (mul_ne_zero hA32.ne' hCneg.ne') hxneg.ne',
    Real.log_mul hA32.ne' hCneg.ne',
    Real.log_rpow hA, Real.log_rpow hC, Real.log_rpow hx,
    Real.log_inv,
    Real.log_mul (pow_ne_zero 2 hC.ne') (pow_ne_zero 3 hM.ne'),
    Real.log_pow, Real.log_pow, hlogA]
  ring

/-- The exact core scale identity in the last display of Section 13.  Here
`N` is `shiftLength x M`; no asymptotic comparison or analytic estimate is
used. -/
theorem section13_core_scale_identity {x C H M : ℝ}
    (hx : 0 < x) (hC : 0 < C) (hH : 0 < H) (hM : 0 < M) :
    Gscale x H M ^ 4 *
        Ascale x C M ^ ((3 : ℝ) / 2) *
        C ^ (-(7 : ℝ) / 2) * H⁻¹ *
        shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
        Kscale x C M ^ 3 * Lscale x C H M ^ 2 *
        x ^ (-(3 : ℝ) / 2) =
      (M / shiftLength x M) * (C / H) ^ 3 * x := by
  have hN : 0 < shiftLength x M := by
    unfold shiftLength
    exact mul_pos hM (Real.rpow_pos_of_pos hx _)
  have hNneg : shiftLength x M ^ (-(5 : ℝ)) =
      (shiftLength x M ^ 5)⁻¹ := by
    calc
      shiftLength x M ^ (-(5 : ℝ)) =
          (shiftLength x M ^ (5 : ℝ))⁻¹ := Real.rpow_neg hN.le 5
      _ = (shiftLength x M ^ 5)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (shiftLength x M) 5)
  rw [hNneg]
  calc
    Gscale x H M ^ 4 *
          Ascale x C M ^ ((3 : ℝ) / 2) *
          C ^ (-(7 : ℝ) / 2) * H⁻¹ *
          (shiftLength x M ^ 5)⁻¹ * M ^ 7 *
          Kscale x C M ^ 3 * Lscale x C H M ^ 2 *
          x ^ (-(3 : ℝ) / 2) =
        (Gscale x H M ^ 4 * H⁻¹ * (shiftLength x M ^ 5)⁻¹ * M ^ 7 *
            Kscale x C M ^ 3 * Lscale x C H M ^ 2) *
          (Ascale x C M ^ ((3 : ℝ) / 2) * C ^ (-(7 : ℝ) / 2) *
            x ^ (-(3 : ℝ) / 2)) := by ring
    _ = (Gscale x H M ^ 4 * H⁻¹ * (shiftLength x M ^ 5)⁻¹ * M ^ 7 *
            Kscale x C M ^ 3 * Lscale x C H M ^ 2) *
          (C ^ 2 * M ^ 3)⁻¹ := by
      rw [section13_halfPowerProduct_eq hx hC hM]
    _ = (M / shiftLength x M) * (C / H) ^ 3 * x := by
      unfold Gscale Kscale Lscale
      field_simp [hx.ne', hC.ne', hH.ne', hM.ne', hN.ne']

/-- The exact quotient `M/N = x^(3/11)` at the named shift scale. -/
theorem section13_M_div_shiftLength_eq {x M : ℝ}
    (hx : 0 < x) (hM : 0 < M) :
    M / shiftLength x M = x ^ ((3 : ℝ) / 11) := by
  rw [shiftLength_eq_mul_rpow]
  have hp : 0 < x ^ (-(3 : ℝ) / 11) := Real.rpow_pos_of_pos hx _
  have hcancel : x ^ ((3 : ℝ) / 11) * x ^ (-(3 : ℝ) / 11) = 1 := by
    rw [← Real.rpow_add hx]
    norm_num
  apply (div_eq_iff (mul_ne_zero hM.ne' hp.ne')).2
  calc
    M = M * 1 := by ring
    _ = M * (x ^ ((3 : ℝ) / 11) * x ^ (-(3 : ℝ) / 11)) := by rw [hcancel]
    _ = x ^ ((3 : ℝ) / 11) * (M * x ^ (-(3 : ℝ) / 11)) := by ring

/-- Consequently `(M/N) x = x^(14/11)` exactly. -/
theorem section13_M_div_shiftLength_mul_x {x M : ℝ}
    (hx : 0 < x) (hM : 0 < M) :
    M / shiftLength x M * x = x ^ ((14 : ℝ) / 11) := by
  calc
    M / shiftLength x M * x = x ^ ((3 : ℝ) / 11) * x := by
      rw [section13_M_div_shiftLength_eq hx hM]
    _ = x ^ ((3 : ℝ) / 11 + 1) := by
      simpa using (Real.rpow_add hx ((3 : ℝ) / 11) 1).symm
    _ = x ^ ((14 : ℝ) / 11) := by congr 1 <;> norm_num

/-- On the main range and under `C ≤ H`, the exact core monomial is bounded
by `x^(14/11)`, which is the scale algebra in the final display of Section 13
before the harmless `x^ε` factor. -/
theorem section13_core_scale_le_fourteen_elevenths {x C H M : ℝ}
    (hmain : InMainRange x H M) (hC : 0 < C) (hCH : C ≤ H) :
    Gscale x H M ^ 4 *
        Ascale x C M ^ ((3 : ℝ) / 2) *
        C ^ (-(7 : ℝ) / 2) * H⁻¹ *
        shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
        Kscale x C M ^ 3 * Lscale x C H M ^ 2 *
        x ^ (-(3 : ℝ) / 2) ≤
      x ^ ((14 : ℝ) / 11) := by
  rcases hmain with ⟨hx, hxM, _, hH, _, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by
    unfold shiftLength
    exact mul_pos hM0 (Real.rpow_pos_of_pos hx0 _)
  have hratio0 : 0 ≤ C / H := div_nonneg hC.le hH0.le
  have hratio1 : C / H ≤ 1 := (div_le_one hH0).2 hCH
  have hratioPow : (C / H) ^ 3 ≤ 1 := pow_le_one₀ hratio0 hratio1
  have hMN0 : 0 ≤ M / shiftLength x M := div_nonneg hM0.le hN0.le
  rw [section13_core_scale_identity hx0 hC hH0 hM0]
  calc
    (M / shiftLength x M) * (C / H) ^ 3 * x ≤
        (M / shiftLength x M) * 1 * x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratioPow hMN0) hx0.le
    _ = M / shiftLength x M * x := by ring
    _ = x ^ ((14 : ℝ) / 11) := section13_M_div_shiftLength_mul_x hx0 hM0

end LeanProofs.IntegerPoints
