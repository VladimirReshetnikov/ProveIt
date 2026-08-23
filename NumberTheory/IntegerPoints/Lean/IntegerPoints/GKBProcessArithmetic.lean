import IntegerPoints.GKBProcessGeometry

/-!
# Graham--Kolesnik B-process: scale arithmetic

This module isolates the real-power algebra and the elementary absorption
inequalities used in the proof of Graham--Kolesnik Theorem 3.10.  Write

`L = y N^(-s)`, `sigma = 1/s`, and `eta = y^(1/s)`.

The main identity below converts the first weighted dual term

`eta^(k+1/2) L^(l-1/2-(k+1/2)/s)`

exactly into the desired B-process scale

`L^(l-1/2) N^(k+1/2)`.

The remaining results compare a dyadic frequency `J` with `L`, normalize the
literal square-root weight and exponent-pair model on a dual block, and absorb
the elementary Lemma 3.6 errors in the small- and large-`L` regimes.  Keeping
these estimates here makes all dependence on `s`, the exponent pair, and the
fixed dyadic endpoint constants explicit.
-/

open Real

namespace LeanProofs.IntegerPoints

namespace GKB

/-! ## Exact primal/dual scale identities -/

/-- Multiplying the dual scale by `N^s` recovers `y`. -/
theorem dualScale_mul_rpow_s {N s y : ℝ} (hN : 0 < N) :
    dualScale N s y * N ^ s = y := by
  unfold dualScale
  rw [mul_assoc, ← Real.rpow_add hN]
  have he : -s + s = (0 : ℝ) := by ring
  rw [he, Real.rpow_zero, mul_one]

/-- The Lemma 3.6 scale is `L N`. -/
theorem phaseScale_eq_dualScale_mul {N s y : ℝ} (hN : 0 < N) :
    phaseScale N s y = dualScale N s y * N := by
  unfold phaseScale dualScale
  have he : 1 - s = -s + 1 := by ring
  rw [he, Real.rpow_add_one hN.ne']
  ring

/-- The inverse-phase coefficient is `eta = L^(1/s) N`. -/
theorem dualEta_eq_dualScale_rpow_mul {N s y : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) :
    y ^ (1 / s) = dualScale N s y ^ (1 / s) * N := by
  have hL : 0 < dualScale N s y := dualScale_pos hN hy
  have he : s * (1 / s) = (1 : ℝ) := by field_simp
  calc
    y ^ (1 / s) = (dualScale N s y * N ^ s) ^ (1 / s) := by
      rw [dualScale_mul_rpow_s (N := N) (s := s) (y := y) hN]
    _ = dualScale N s y ^ (1 / s) * (N ^ s) ^ (1 / s) := by
      rw [Real.mul_rpow hL.le (Real.rpow_nonneg hN.le s)]
    _ = dualScale N s y ^ (1 / s) * N ^ (s * (1 / s)) := by
      rw [← Real.rpow_mul hN.le]
    _ = dualScale N s y ^ (1 / s) * N := by rw [he, Real.rpow_one]

/-- The reciprocal remainder in `IsExponentPair` is exactly `L⁻¹`. -/
theorem inv_dualScale_eq {N s y : ℝ} (hN : 0 < N) :
    (dualScale N s y)⁻¹ = y⁻¹ * N ^ s := by
  unfold dualScale
  rw [mul_inv, Real.rpow_neg hN.le, inv_inv]

/--
Exact conversion of the normalized first dual term to the B-process main
scale.  This is the central exponent identity in Theorem 3.10.
-/
theorem dual_main_scale_identity {N s y k l : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) :
    (y ^ (1 / s)) ^ (k + 1 / 2) *
        (dualScale N s y) ^ (l - 1 / 2 - (k + 1 / 2) / s) =
      (dualScale N s y) ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by
  have hL : 0 < dualScale N s y := dualScale_pos hN hy
  rw [dualEta_eq_dualScale_rpow_mul hN hs hy,
    Real.mul_rpow (Real.rpow_nonneg hL.le (1 / s)) hN.le,
    ← Real.rpow_mul hL.le]
  calc
    (dualScale N s y) ^ ((1 / s) * (k + 1 / 2)) * N ^ (k + 1 / 2) *
          (dualScale N s y) ^ (l - 1 / 2 - (k + 1 / 2) / s) =
        ((dualScale N s y) ^ ((1 / s) * (k + 1 / 2)) *
          (dualScale N s y) ^ (l - 1 / 2 - (k + 1 / 2) / s)) *
            N ^ (k + 1 / 2) := by ring
    _ = (dualScale N s y) ^
          ((1 / s) * (k + 1 / 2) +
            (l - 1 / 2 - (k + 1 / 2) / s)) * N ^ (k + 1 / 2) := by
      rw [← Real.rpow_add hL]
    _ = (dualScale N s y) ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by
      congr 2
      ring

/-- The second weighted dual monomial is exactly `F^(-1/2)` at `J = L`. -/
theorem dual_error_scale_identity {N s y : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) :
    (y ^ (1 / s)) ^ (-(1 : ℝ) / 2) *
        (dualScale N s y) ^ (-(1 : ℝ) / 2 + 1 / (2 * s)) =
      phaseScale N s y ^ (-(1 : ℝ) / 2) := by
  have hL : 0 < dualScale N s y := dualScale_pos hN hy
  rw [dualEta_eq_dualScale_rpow_mul hN hs hy,
    Real.mul_rpow (Real.rpow_nonneg hL.le (1 / s)) hN.le,
    ← Real.rpow_mul hL.le, phaseScale_eq_dualScale_mul hN,
    Real.mul_rpow hL.le hN.le]
  calc
    (dualScale N s y) ^ ((1 / s) * (-(1 : ℝ) / 2)) *
          N ^ (-(1 : ℝ) / 2) *
          (dualScale N s y) ^ (-(1 : ℝ) / 2 + 1 / (2 * s)) =
        ((dualScale N s y) ^ ((1 / s) * (-(1 : ℝ) / 2)) *
          (dualScale N s y) ^ (-(1 : ℝ) / 2 + 1 / (2 * s))) *
            N ^ (-(1 : ℝ) / 2) := by ring
    _ = (dualScale N s y) ^
          ((1 / s) * (-(1 : ℝ) / 2) +
            (-(1 : ℝ) / 2 + 1 / (2 * s))) * N ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_add hL]
    _ = (dualScale N s y) ^ (-(1 : ℝ) / 2) * N ^ (-(1 : ℝ) / 2) := by
      congr 2
      field_simp
      ring

/-! ## The literal weighted dual model -/

/-- The upper square-root model for the dual stationary weight. -/
noncomputable def dualModelWeight (sigma eta J : ℝ) : ℝ :=
  Real.sqrt (5 / 4 * sigma * eta * J ^ (-sigma - 1))

/-- Split the literal square-root model into its coefficient, `eta`, and `J` powers. -/
theorem dualModelWeight_eq {sigma eta J : ℝ}
    (hsigma : 0 < sigma) (heta : 0 < eta) (hJ : 0 < J) :
    dualModelWeight sigma eta J =
      Real.sqrt (5 / 4 * sigma) * eta ^ (1 / 2 : ℝ) *
        J ^ ((-sigma - 1) / 2) := by
  unfold dualModelWeight
  simp only [Real.sqrt_eq_rpow]
  have hc : 0 ≤ 5 / 4 * sigma := by positivity
  calc
    (5 / 4 * sigma * eta * J ^ (-sigma - 1)) ^ (1 / 2 : ℝ) =
        (5 / 4 * sigma * eta) ^ (1 / 2 : ℝ) *
          (J ^ (-sigma - 1)) ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (mul_nonneg hc heta.le) (Real.rpow_nonneg hJ.le _)]
    _ = (5 / 4 * sigma) ^ (1 / 2 : ℝ) * eta ^ (1 / 2 : ℝ) *
          J ^ ((-sigma - 1) * (1 / 2 : ℝ)) := by
      rw [Real.mul_rpow hc heta.le, ← Real.rpow_mul hJ.le]
    _ = (5 / 4 * sigma) ^ (1 / 2 : ℝ) * eta ^ (1 / 2 : ℝ) *
          J ^ ((-sigma - 1) / 2) := by
      rw [show (-sigma - 1) * (1 / 2 : ℝ) = (-sigma - 1) / 2 by ring]

/-- Normalize the first term in the literal weighted exponent-pair model. -/
theorem dualModelWeight_mul_main_eq {sigma eta J k l : ℝ}
    (hsigma : 0 < sigma) (heta : 0 < eta) (hJ : 0 < J) :
    dualModelWeight sigma eta J *
        ((eta * J ^ (-sigma)) ^ k * J ^ l) =
      Real.sqrt (5 / 4 * sigma) *
        (eta ^ (k + 1 / 2) *
          J ^ (l - 1 / 2 - (k + 1 / 2) * sigma)) := by
  rw [dualModelWeight_eq hsigma heta hJ,
    Real.mul_rpow heta.le (Real.rpow_nonneg hJ.le (-sigma)),
    ← Real.rpow_mul hJ.le]
  calc
    Real.sqrt (5 / 4 * sigma) * eta ^ (1 / 2 : ℝ) *
          J ^ ((-sigma - 1) / 2) *
          (eta ^ k * J ^ ((-sigma) * k) * J ^ l) =
        Real.sqrt (5 / 4 * sigma) *
          ((eta ^ (1 / 2 : ℝ) * eta ^ k) *
            ((J ^ ((-sigma - 1) / 2) * J ^ ((-sigma) * k)) * J ^ l)) := by
      ring
    _ = Real.sqrt (5 / 4 * sigma) *
          (eta ^ ((1 / 2 : ℝ) + k) *
            (J ^ (((-sigma - 1) / 2) + (-sigma) * k) * J ^ l)) := by
      rw [← Real.rpow_add heta, ← Real.rpow_add hJ]
    _ = Real.sqrt (5 / 4 * sigma) *
          (eta ^ ((1 / 2 : ℝ) + k) *
            J ^ (((-sigma - 1) / 2) + (-sigma) * k + l)) := by
      rw [← Real.rpow_add hJ]
    _ = Real.sqrt (5 / 4 * sigma) *
        (eta ^ (k + 1 / 2) *
          J ^ (l - 1 / 2 - (k + 1 / 2) * sigma)) := by
      congr 3 <;> ring

/-- Normalize the reciprocal term in the literal weighted exponent-pair model. -/
theorem dualModelWeight_mul_error_eq {sigma eta J : ℝ}
    (hsigma : 0 < sigma) (heta : 0 < eta) (hJ : 0 < J) :
    dualModelWeight sigma eta J * (eta⁻¹ * J ^ sigma) =
      Real.sqrt (5 / 4 * sigma) *
        (eta ^ (-(1 : ℝ) / 2) * J ^ (-(1 : ℝ) / 2 + sigma / 2)) := by
  rw [dualModelWeight_eq hsigma heta hJ, ← Real.rpow_neg_one eta]
  calc
    Real.sqrt (5 / 4 * sigma) * eta ^ (1 / 2 : ℝ) *
          J ^ ((-sigma - 1) / 2) * (eta ^ (-(1 : ℝ)) * J ^ sigma) =
        Real.sqrt (5 / 4 * sigma) *
          ((eta ^ (1 / 2 : ℝ) * eta ^ (-(1 : ℝ))) *
            (J ^ ((-sigma - 1) / 2) * J ^ sigma)) := by ring
    _ = Real.sqrt (5 / 4 * sigma) *
          (eta ^ ((1 / 2 : ℝ) + (-(1 : ℝ))) *
            J ^ ((-sigma - 1) / 2 + sigma)) := by
      rw [← Real.rpow_add heta, ← Real.rpow_add hJ]
    _ = Real.sqrt (5 / 4 * sigma) *
        (eta ^ (-(1 : ℝ) / 2) * J ^ (-(1 : ℝ) / 2 + sigma / 2)) := by
      congr 3 <;> ring

/-- Distribute and normalize the complete literal weighted dual model. -/
theorem dualModelWeight_mul_model_eq {sigma eta J k l : ℝ}
    (hsigma : 0 < sigma) (heta : 0 < eta) (hJ : 0 < J) :
    dualModelWeight sigma eta J *
        ((eta * J ^ (-sigma)) ^ k * J ^ l + eta⁻¹ * J ^ sigma) =
      Real.sqrt (5 / 4 * sigma) *
        (eta ^ (k + 1 / 2) *
            J ^ (l - 1 / 2 - (k + 1 / 2) * sigma) +
          eta ^ (-(1 : ℝ) / 2) * J ^ (-(1 : ℝ) / 2 + sigma / 2)) := by
  rw [mul_add, dualModelWeight_mul_main_eq hsigma heta hJ,
    dualModelWeight_mul_error_eq hsigma heta hJ]
  ring

/-! ## Comparing a dyadic frequency with the dual scale -/

/--
If `J` lies between fixed positive multiples of `L`, then every real power of
`J` is controlled by the corresponding power of `L`.  The maximum handles
both signs of the exponent without a case distinction in callers.
-/
theorem rpow_le_max_mul_rpow_of_mul_le {c₀ c₁ L J r : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hL : 0 < L)
    (hlower : c₀ * L ≤ J) (hupper : J ≤ c₁ * L) :
    J ^ r ≤ max (c₀ ^ r) (c₁ ^ r) * L ^ r := by
  have hJ : 0 < J := (mul_pos hc₀ hL).trans_le hlower
  rcases le_total 0 r with hr | hr
  · calc
      J ^ r ≤ (c₁ * L) ^ r := Real.rpow_le_rpow hJ.le hupper hr
      _ = c₁ ^ r * L ^ r := Real.mul_rpow hc₁.le hL.le
      _ ≤ max (c₀ ^ r) (c₁ ^ r) * L ^ r :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hL.le r)
  · calc
      J ^ r ≤ (c₀ * L) ^ r :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hc₀ hL) hlower hr
      _ = c₀ ^ r * L ^ r := Real.mul_rpow hc₀.le hL.le
      _ ≤ max (c₀ ^ r) (c₁ ^ r) * L ^ r :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hL.le r)

/-- Dyadic comparison followed by the exact main-scale conversion. -/
theorem dual_block_main_scale_le {N s y k l c₀ c₁ J : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hlower : c₀ * dualScale N s y ≤ J)
    (hupper : J ≤ c₁ * dualScale N s y) :
    (y ^ (1 / s)) ^ (k + 1 / 2) *
        J ^ (l - 1 / 2 - (k + 1 / 2) / s) ≤
      max (c₀ ^ (l - 1 / 2 - (k + 1 / 2) / s))
          (c₁ ^ (l - 1 / 2 - (k + 1 / 2) / s)) *
        ((dualScale N s y) ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by
  have hL : 0 < dualScale N s y := dualScale_pos (s := s) hN hy
  have hcompare := rpow_le_max_mul_rpow_of_mul_le hc₀ hc₁ hL hlower hupper
    (r := l - 1 / 2 - (k + 1 / 2) / s)
  calc
    (y ^ (1 / s)) ^ (k + 1 / 2) *
          J ^ (l - 1 / 2 - (k + 1 / 2) / s) ≤
        (y ^ (1 / s)) ^ (k + 1 / 2) *
          (max (c₀ ^ (l - 1 / 2 - (k + 1 / 2) / s))
              (c₁ ^ (l - 1 / 2 - (k + 1 / 2) / s)) *
            (dualScale N s y) ^ (l - 1 / 2 - (k + 1 / 2) / s)) :=
      mul_le_mul_of_nonneg_left hcompare (Real.rpow_nonneg (Real.rpow_nonneg hy.le _) _)
    _ = max (c₀ ^ (l - 1 / 2 - (k + 1 / 2) / s))
          (c₁ ^ (l - 1 / 2 - (k + 1 / 2) / s)) *
        ((y ^ (1 / s)) ^ (k + 1 / 2) *
          (dualScale N s y) ^ (l - 1 / 2 - (k + 1 / 2) / s)) := by ring
    _ = max (c₀ ^ (l - 1 / 2 - (k + 1 / 2) / s))
          (c₁ ^ (l - 1 / 2 - (k + 1 / 2) / s)) *
        ((dualScale N s y) ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by
      rw [dual_main_scale_identity hN hs hy]

/-- Dyadic comparison followed by the exact second-term conversion. -/
theorem dual_block_error_scale_le {N s y c₀ c₁ J : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hlower : c₀ * dualScale N s y ≤ J)
    (hupper : J ≤ c₁ * dualScale N s y) :
    (y ^ (1 / s)) ^ (-(1 : ℝ) / 2) * J ^ (-(1 : ℝ) / 2 + 1 / (2 * s)) ≤
      max (c₀ ^ (-(1 : ℝ) / 2 + 1 / (2 * s)))
          (c₁ ^ (-(1 : ℝ) / 2 + 1 / (2 * s))) *
        phaseScale N s y ^ (-(1 : ℝ) / 2) := by
  have hL : 0 < dualScale N s y := dualScale_pos (s := s) hN hy
  have hcompare := rpow_le_max_mul_rpow_of_mul_le hc₀ hc₁ hL hlower hupper
    (r := -(1 : ℝ) / 2 + 1 / (2 * s))
  calc
    (y ^ (1 / s)) ^ (-(1 : ℝ) / 2) *
          J ^ (-(1 : ℝ) / 2 + 1 / (2 * s)) ≤
        (y ^ (1 / s)) ^ (-(1 : ℝ) / 2) *
          (max (c₀ ^ (-(1 : ℝ) / 2 + 1 / (2 * s)))
              (c₁ ^ (-(1 : ℝ) / 2 + 1 / (2 * s))) *
            (dualScale N s y) ^ (-(1 : ℝ) / 2 + 1 / (2 * s))) :=
      mul_le_mul_of_nonneg_left hcompare (Real.rpow_nonneg (Real.rpow_nonneg hy.le _) _)
    _ = max (c₀ ^ (-(1 : ℝ) / 2 + 1 / (2 * s)))
          (c₁ ^ (-(1 : ℝ) / 2 + 1 / (2 * s))) *
        ((y ^ (1 / s)) ^ (-(1 : ℝ) / 2) *
          (dualScale N s y) ^ (-(1 : ℝ) / 2 + 1 / (2 * s))) := by ring
    _ = max (c₀ ^ (-(1 : ℝ) / 2 + 1 / (2 * s)))
          (c₁ ^ (-(1 : ℝ) / 2 + 1 / (2 * s))) *
        phaseScale N s y ^ (-(1 : ℝ) / 2) := by
      rw [dual_error_scale_identity hN hs hy]

/-! ## Small- and large-scale absorption -/

/-- In the small-`L` regime the `(1/2,1/2)` bound is below the B main term. -/
theorem sqrt_mul_le_bMain_of_le_one {N L k l : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hLone : L ≤ 1)
    (hk : 0 ≤ k) (hl : l ≤ 1) :
    Real.sqrt (L * N) ≤ L ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hL.le hNpos.le]
  have hLpow : L ^ (1 / 2 : ℝ) ≤ L ^ (l - 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hL hLone (by linarith)
  have hNpow : N ^ (1 / 2 : ℝ) ≤ N ^ (k + 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  exact mul_le_mul hLpow hNpow (Real.rpow_nonneg hNpos.le _)
    (Real.rpow_nonneg hL.le _)

/-- Normalize the second error term of Lemma 3.6 to `L^(-1/2) N^(1/2)`. -/
theorem phaseScale_neg_half_mul_eq {N s y : ℝ}
    (hN : 0 < N) (hy : 0 < y) :
    phaseScale N s y ^ (-(1 : ℝ) / 2) * N =
      dualScale N s y ^ (-(1 : ℝ) / 2) * N ^ (1 / 2 : ℝ) := by
  have hL : 0 < dualScale N s y := dualScale_pos hN hy
  rw [phaseScale_eq_dualScale_mul hN, Real.mul_rpow hL.le hN.le]
  calc
    dualScale N s y ^ (-(1 : ℝ) / 2) * N ^ (-(1 : ℝ) / 2) * N =
        dualScale N s y ^ (-(1 : ℝ) / 2) *
          (N ^ (-(1 : ℝ) / 2) * N ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = dualScale N s y ^ (-(1 : ℝ) / 2) *
          N ^ (-(1 : ℝ) / 2 + 1) := by rw [← Real.rpow_add hN]
    _ = dualScale N s y ^ (-(1 : ℝ) / 2) * N ^ (1 / 2 : ℝ) := by norm_num

/-- For `N,L ≥ 1`, the Lemma 3.6 power error is bounded by the B main term. -/
theorem phaseScale_neg_half_mul_le_bMain {N s y k l : ℝ}
    (hN : 1 ≤ N) (hy : 0 < y) (hL : 1 ≤ dualScale N s y)
    (hk : 0 ≤ k) (hl : 1 / 2 ≤ l) :
    phaseScale N s y ^ (-(1 : ℝ) / 2) * N ≤
      dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  rw [phaseScale_neg_half_mul_eq hNpos hy]
  have hLpow : dualScale N s y ^ (-(1 : ℝ) / 2) ≤
      dualScale N s y ^ (l - 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hNpow : N ^ (1 / 2 : ℝ) ≤ N ^ (k + 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  exact mul_le_mul hLpow hNpow (Real.rpow_nonneg hNpos.le _)
    (Real.rpow_nonneg (by positivity) _)

/-- A fixed nonnegative multiple of the Lemma 3.6 error is absorbed likewise. -/
theorem mul_phaseScale_neg_half_mul_le_bMain {N s y k l C : ℝ}
    (hN : 1 ≤ N) (hy : 0 < y) (hL : 1 ≤ dualScale N s y)
    (hk : 0 ≤ k) (hl : 1 / 2 ≤ l) (hC : 0 ≤ C) :
    C * (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) ≤
      C * (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) :=
  mul_le_mul_of_nonneg_left
    (phaseScale_neg_half_mul_le_bMain hN hy hL hk hl) hC

/-- The B main scale itself is at least one when both basic scales are large. -/
theorem one_le_bMain_of_one_le {N L k l : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hk : 0 ≤ k) (hl : 1 / 2 ≤ l) :
    1 ≤ L ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by
  exact one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hL (by linarith))
    (Real.one_le_rpow hN (by linarith))

/-- Any fixed nonnegative endpoint contribution is absorbed by that main scale. -/
theorem fixed_le_mul_bMain_of_one_le {N L k l C : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hk : 0 ≤ k) (hl : 1 / 2 ≤ l) (hC : 0 ≤ C) :
    C ≤ C * (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by
  calc
    C = C * 1 := by ring
    _ ≤ C * (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) :=
      mul_le_mul_of_nonneg_left (one_le_bMain_of_one_le hN hL hk hl) hC

/-- Absorb a fixed multiple of the Lemma 3.6 error and a fixed endpoint term together. -/
theorem phaseScale_error_add_fixed_le_bMain {N s y k l C₁ C₂ : ℝ}
    (hN : 1 ≤ N) (hy : 0 < y) (hL : 1 ≤ dualScale N s y)
    (hk : 0 ≤ k) (hl : 1 / 2 ≤ l) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    C₁ * (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) + C₂ ≤
      (C₁ + C₂) *
        (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by
  calc
    C₁ * (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) + C₂ ≤
        C₁ * (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
          C₂ * (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) :=
      add_le_add
        (mul_phaseScale_neg_half_mul_le_bMain hN hy hL hk hl hC₁)
        (fixed_le_mul_bMain_of_one_le hN hL hk hl hC₂)
    _ = (C₁ + C₂) *
        (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by ring

/-! ## Logarithmic and short-interval absorption -/

/-- An explicit power bound for `log (L+2)` on `L ≥ 1`. -/
theorem log_add_two_le_rpow {delta L : ℝ} (hdelta : 0 < delta) (hL : 1 ≤ L) :
    Real.log (L + 2) ≤ (Real.log 3 + delta⁻¹) * L ^ delta := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hLadd : L + 2 ≤ 3 * L := by linarith
  have hpow : 1 ≤ L ^ delta := Real.one_le_rpow hL hdelta.le
  have hlogpow := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hLpos delta)
  rw [Real.log_rpow hLpos] at hlogpow
  have hlogL : Real.log L ≤ L ^ delta / delta := by
    apply (le_div_iff₀ hdelta).2
    nlinarith
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc
    Real.log (L + 2) ≤ Real.log (3 * L) :=
      Real.log_le_log (by positivity) hLadd
    _ = Real.log 3 + Real.log L := Real.log_mul (by norm_num) hLpos.ne'
    _ ≤ Real.log 3 + L ^ delta / delta := add_le_add le_rfl hlogL
    _ ≤ Real.log 3 * L ^ delta + (1 / delta) * L ^ delta := by
      have hfirst : Real.log 3 ≤ Real.log 3 * L ^ delta := by
        calc
          Real.log 3 = Real.log 3 * 1 := by ring
          _ ≤ Real.log 3 * L ^ delta := mul_le_mul_of_nonneg_left hpow hlog3
      have hsecond : L ^ delta / delta = (1 / delta) * L ^ delta := by ring
      rw [hsecond]
      exact add_le_add hfirst le_rfl
    _ = (Real.log 3 + delta⁻¹) * L ^ delta := by
      rw [one_div]
      ring

/-- Existential form emphasizing that the logarithmic constant depends only on `delta`. -/
theorem exists_log_add_two_le_rpow {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → Real.log (L + 2) ≤ C * L ^ delta := by
  refine ⟨Real.log 3 + delta⁻¹, ?_, ?_⟩
  · have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  · intro L hL
    exact log_add_two_le_rpow hdelta hL

/--
If a short interval is nonempty then `N ≥ 1/2`; in the regime `N < 1` this
forces the target B-process right-hand side to be at least `1/2`.
-/
theorem half_le_bRhs_of_half_le_N_of_lt_one {N L k l : ℝ}
    (hNhalf : 1 / 2 ≤ N) (hNone : N < 1) (hL : 0 < L)
    (hk : k ≤ 1 / 2) (hl : 1 / 2 ≤ l) :
    1 / 2 ≤ L ^ (l - 1 / 2) * N ^ (k + 1 / 2) + L⁻¹ := by
  have hN : 0 < N := by linarith
  rcases le_or_gt 1 L with hLone | hLone
  · have hLp : 1 ≤ L ^ (l - 1 / 2) := Real.one_le_rpow hLone (by linarith)
    have hNp : N ≤ N ^ (k + 1 / 2) := by
      calc
        N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
        _ ≤ N ^ (k + 1 / 2) :=
          Real.rpow_le_rpow_of_exponent_ge hN hNone.le (by linarith)
    have hmain : N ≤ L ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by
      calc
        N ≤ 1 * N ^ (k + 1 / 2) := by simpa using hNp
        _ ≤ L ^ (l - 1 / 2) * N ^ (k + 1 / 2) :=
          mul_le_mul_of_nonneg_right hLp (Real.rpow_nonneg hN.le _)
    have hinv : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
    linarith
  · have hinv : 1 < L⁻¹ := (one_lt_inv₀ hL).2 hLone
    have hmain : 0 ≤ L ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by positivity
    linarith

/-- The form used to dominate a single unit-norm summand by twice the target RHS. -/
theorem one_le_two_mul_bRhs_of_half_le_N_of_lt_one {N L k l : ℝ}
    (hNhalf : 1 / 2 ≤ N) (hNone : N < 1) (hL : 0 < L)
    (hk : k ≤ 1 / 2) (hl : 1 / 2 ≤ l) :
    1 ≤ 2 * (L ^ (l - 1 / 2) * N ^ (k + 1 / 2) + L⁻¹) := by
  linarith [half_le_bRhs_of_half_le_N_of_lt_one hNhalf hNone hL hk hl]

end GKB

end LeanProofs.IntegerPoints
