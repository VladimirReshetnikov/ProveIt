import IntegerPoints.GKBProcessMainTerm

/-!
# Graham--Kolesnik B-process: normalization of the stationary main term

`GKBProcessMainTerm` bounds the closed stationary sum by a finite sum of
explicit dyadic block models, two literal stationary endpoint weights, and
one possible dual upper-endpoint model.  This module normalizes all of those
terms to the two scales

`L^(l-1/2) N^(k+1/2)` and `F^(-1/2) N`,

where `L = dualScale N s y` and `F = phaseScale N s y = L N`.

The public dyadic sum includes an explicit upper bound even for a late block
whose actual frequency range is empty.  Consequently all `j < dyadicDepth s`
are compared with `L` using the deliberately broad fixed interval

`endpointLower s * L <= J <=
  (2^dyadicDepth s * endpointUpper) * L`.

The terminal scale lies between the true derivative endpoints and therefore
uses the sharper upper multiple `endpointUpper`.

All coefficients below depend only on `k`, `l`, `s`, and the fixed parameter
package.  The first final theorem retains both natural scales.  In the regime
`N,L >= 1`, `0 <= k`, and `1/2 <= l`, the second final theorem absorbs
`F^(-1/2) N` into the B-main scale.
-/

open scoped BigOperators
open Real Finset Set

namespace LeanProofs.IntegerPoints

namespace GKB

/-! ## Fixed comparison exponents and constants -/

/-- The broad upper multiple valid for every explicit dyadic block model. -/
noncomputable def blockUpperMultiple (s : ℝ) : ℝ :=
  (2 : ℝ) ^ dyadicDepth s * endpointUpper

/-- The exponent of `J` in the normalized main block monomial. -/
noncomputable def blockMainExponent (k l s : ℝ) : ℝ :=
  l - 1 / 2 - (k + 1 / 2) / s

/-- The exponent of `J` in the reciprocal block monomial. -/
noncomputable def blockErrorExponent (s : ℝ) : ℝ :=
  -(1 : ℝ) / 2 + 1 / (2 * s)

/-- The exponent of `J` in the dual stationary weight itself. -/
noncomputable def dualWeightExponent (s : ℝ) : ℝ :=
  (-(1 / s) - 1) / 2

/-- The fixed square-root coefficient in every dual model weight. -/
noncomputable def dualSqrtFactor (s : ℝ) : ℝ :=
  Real.sqrt (5 / 4 * (1 / s))

/-- Worst main-monomial ratio over every explicit dyadic block. -/
noncomputable def blockMainRatio (k l s : ℝ) : ℝ :=
  max ((endpointLower s) ^ blockMainExponent k l s)
    ((blockUpperMultiple s) ^ blockMainExponent k l s)

/-- Worst reciprocal-monomial ratio over every explicit dyadic block. -/
noncomputable def blockErrorRatio (s : ℝ) : ℝ :=
  max ((endpointLower s) ^ blockErrorExponent s)
    ((blockUpperMultiple s) ^ blockErrorExponent s)

/-- Worst stationary-weight ratio on the terminal interval. -/
noncomputable def terminalWeightRatio (s : ℝ) : ℝ :=
  max ((endpointLower s) ^ dualWeightExponent s)
    (endpointUpper ^ dualWeightExponent s)

/-- Coefficient of the B-main scale contributed by all dyadic blocks. -/
noncomputable def mainBoundMainCoefficient
    {k l s : ℝ} (params : Parameters k l s) : ℝ :=
  (dyadicDepth s : ℝ) * params.pairConstant * dualSqrtFactor s *
    blockMainRatio k l s

/-- Coefficient of `F^(-1/2) N` contributed by the reciprocal block terms and
all three possible endpoint costs. -/
noncomputable def mainBoundErrorCoefficient
    {k l s : ℝ} (params : Parameters k l s) : ℝ :=
  (dyadicDepth s : ℝ) * params.pairConstant * dualSqrtFactor s *
      blockErrorRatio s +
    2 * curvatureLower s ^ (-(1 : ℝ) / 2) +
    dualSqrtFactor s * terminalWeightRatio s

/-- One coefficient dominating the complete normalized stationary main term. -/
noncomputable def mainBoundConstant
    {k l s : ℝ} (params : Parameters k l s) : ℝ :=
  mainBoundMainCoefficient params + mainBoundErrorCoefficient params

theorem blockUpperMultiple_pos (s : ℝ) :
    0 < blockUpperMultiple s := by
  unfold blockUpperMultiple
  have hendpoint : 0 < endpointUpper := (endpointConstants_pos s).2.1
  positivity

theorem dualSqrtFactor_pos {s : ℝ} (hs : 0 < s) :
    0 < dualSqrtFactor s := by
  unfold dualSqrtFactor
  positivity

theorem blockMainRatio_pos (k l s : ℝ) :
    0 < blockMainRatio k l s := by
  unfold blockMainRatio
  exact lt_of_lt_of_le
    (Real.rpow_pos_of_pos (endpointConstants_pos s).1 _)
    (le_max_left _ _)

theorem blockErrorRatio_pos (s : ℝ) :
    0 < blockErrorRatio s := by
  unfold blockErrorRatio
  exact lt_of_lt_of_le
    (Real.rpow_pos_of_pos (endpointConstants_pos s).1 _)
    (le_max_left _ _)

theorem terminalWeightRatio_pos (s : ℝ) :
    0 < terminalWeightRatio s := by
  unfold terminalWeightRatio
  exact lt_of_lt_of_le
    (Real.rpow_pos_of_pos (endpointConstants_pos s).1 _)
    (le_max_left _ _)

theorem mainBoundMainCoefficient_nonneg
    {k l s : ℝ} (params : Parameters k l s) (hs : 0 < s) :
    0 ≤ mainBoundMainCoefficient params := by
  unfold mainBoundMainCoefficient
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) params.pairConstant_nonneg)
      (dualSqrtFactor_pos hs).le)
    (blockMainRatio_pos k l s).le

theorem mainBoundErrorCoefficient_nonneg
    {k l s : ℝ} (params : Parameters k l s) (hs : 0 < s) :
    0 ≤ mainBoundErrorCoefficient params := by
  unfold mainBoundErrorCoefficient
  have hcurv : 0 < curvatureLower s := (curvatureConstants_pos hs).1
  have hblocks : 0 ≤ (dyadicDepth s : ℝ) * params.pairConstant *
      dualSqrtFactor s * blockErrorRatio s :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) params.pairConstant_nonneg)
        (dualSqrtFactor_pos hs).le)
      (blockErrorRatio_pos s).le
  have hstationary : 0 ≤ 2 * curvatureLower s ^ (-(1 : ℝ) / 2) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hcurv.le _)
  have hterminal : 0 ≤ dualSqrtFactor s * terminalWeightRatio s :=
    mul_nonneg (dualSqrtFactor_pos hs).le (terminalWeightRatio_pos s).le
  exact add_nonneg (add_nonneg hblocks hstationary) hterminal

theorem mainBoundConstant_nonneg
    {k l s : ℝ} (params : Parameters k l s) (hs : 0 < s) :
    0 ≤ mainBoundConstant params := by
  unfold mainBoundConstant
  exact add_nonneg
    (mainBoundMainCoefficient_nonneg params hs)
    (mainBoundErrorCoefficient_nonneg params hs)

/-! ## Exact normalization of a bare dual weight -/

/-- At `J = L`, the dual stationary-weight monomial is exactly
`F^(-1/2) N`. -/
theorem dual_weight_scale_identity {N s y : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) :
    (y ^ (1 / s)) ^ (1 / 2 : ℝ) *
        (dualScale N s y) ^ dualWeightExponent s =
      phaseScale N s y ^ (-(1 : ℝ) / 2) * N := by
  have hL : 0 < dualScale N s y := dualScale_pos (s := s) hN hy
  have hLexp :
      (1 / s) * (1 / 2 : ℝ) + dualWeightExponent s = -(1 : ℝ) / 2 := by
    unfold dualWeightExponent
    field_simp [hs.ne']
    ring_nf
  have hNpow :
      N ^ (-(1 : ℝ) / 2) * N = N ^ (1 / 2 : ℝ) := by
    calc
      N ^ (-(1 : ℝ) / 2) * N =
          N ^ (-(1 : ℝ) / 2) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = N ^ (-(1 : ℝ) / 2 + 1) := by rw [← Real.rpow_add hN]
      _ = N ^ (1 / 2 : ℝ) := by norm_num
  rw [dualEta_eq_dualScale_rpow_mul hN hs hy,
    Real.mul_rpow (Real.rpow_nonneg hL.le _) hN.le,
    ← Real.rpow_mul hL.le,
    phaseScale_eq_dualScale_mul hN,
    Real.mul_rpow hL.le hN.le]
  calc
    dualScale N s y ^ ((1 / s) * (1 / 2 : ℝ)) * N ^ (1 / 2 : ℝ) *
          dualScale N s y ^ dualWeightExponent s =
        (dualScale N s y ^ ((1 / s) * (1 / 2 : ℝ)) *
          dualScale N s y ^ dualWeightExponent s) * N ^ (1 / 2 : ℝ) := by ring_nf
    _ = dualScale N s y ^
          ((1 / s) * (1 / 2 : ℝ) + dualWeightExponent s) *
            N ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hL]
    _ = dualScale N s y ^ (-(1 : ℝ) / 2) * N ^ (1 / 2 : ℝ) := by
      rw [hLexp]
    _ = dualScale N s y ^ (-(1 : ℝ) / 2) *
          (N ^ (-(1 : ℝ) / 2) * N) := by rw [hNpow]
    _ = dualScale N s y ^ (-(1 : ℝ) / 2) *
          N ^ (-(1 : ℝ) / 2) * N := by ring_nf

/-- Compare a bare dual model weight at any `J` lying between two fixed
positive multiples of `L`. -/
theorem dualModelWeight_le_largeErrorScale
    {N s y c₀ c₁ J : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hlower : c₀ * dualScale N s y ≤ J)
    (hupper : J ≤ c₁ * dualScale N s y) :
    dualModelWeight (1 / s) (y ^ (1 / s)) J ≤
      dualSqrtFactor s *
        max (c₀ ^ dualWeightExponent s) (c₁ ^ dualWeightExponent s) *
          (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
  have hL : 0 < dualScale N s y := dualScale_pos (s := s) hN hy
  have hJ : 0 < J := (mul_pos hc₀ hL).trans_le hlower
  have heta : 0 < y ^ (1 / s) := Real.rpow_pos_of_pos hy _
  have hsigma : 0 < 1 / s := by positivity
  have hpow := rpow_le_max_mul_rpow_of_mul_le hc₀ hc₁ hL hlower hupper
    (r := dualWeightExponent s)
  rw [dualModelWeight_eq hsigma heta hJ]
  have hexp : (-(1 / s) - 1) / 2 = dualWeightExponent s := rfl
  rw [hexp]
  calc
    Real.sqrt (5 / 4 * (1 / s)) * (y ^ (1 / s)) ^ (1 / 2 : ℝ) *
          J ^ dualWeightExponent s ≤
        Real.sqrt (5 / 4 * (1 / s)) * (y ^ (1 / s)) ^ (1 / 2 : ℝ) *
          (max (c₀ ^ dualWeightExponent s) (c₁ ^ dualWeightExponent s) *
            dualScale N s y ^ dualWeightExponent s) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = dualSqrtFactor s *
        max (c₀ ^ dualWeightExponent s) (c₁ ^ dualWeightExponent s) *
          ((y ^ (1 / s)) ^ (1 / 2 : ℝ) *
            dualScale N s y ^ dualWeightExponent s) := by
      unfold dualSqrtFactor
      ring_nf
    _ = dualSqrtFactor s *
        max (c₀ ^ dualWeightExponent s) (c₁ ^ dualWeightExponent s) *
          (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
      rw [dual_weight_scale_identity hN hs hy]

/-! ## Uniform comparison of the explicit dyadic and terminal scales -/

/-- Every explicit dyadic left endpoint occurring in the public finite sum is
between fixed multiples of `L`, including those whose actual truncated block
has already become empty. -/
theorem dyadicCut_deriv_comparable
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f)
    {j : ℕ} (hj : j < dyadicDepth s) :
    endpointLower s * dualScale N s y ≤ dyadicCut (deriv f b) j ∧
      dyadicCut (deriv f b) j ≤ blockUpperMultiple s * dualScale N s y := by
  have hends := endpoint_derivative_bounds hN hs hy hP heps hf
  have hAlphaUpper : deriv f b < endpointUpper * dualScale N s y :=
    hends.2.2.2.1.trans_lt hends.2.2.2.2
  have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ dyadicDepth s :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hj)
  constructor
  · have hAlphaCut : deriv f b ≤ dyadicCut (deriv f b) j := by
      calc
        deriv f b = dyadicCut (deriv f b) 0 := (dyadicCut_zero _).symm
        _ ≤ dyadicCut (deriv f b) j :=
          dyadicCut_monotone hends.2.2.1.le (Nat.zero_le j)
    exact hends.2.1.le.trans hAlphaCut
  · calc
      dyadicCut (deriv f b) j = (2 : ℝ) ^ j * deriv f b := rfl
      _ ≤ (2 : ℝ) ^ j * (endpointUpper * dualScale N s y) :=
        mul_le_mul_of_nonneg_left hAlphaUpper.le (by positivity)
      _ ≤ (2 : ℝ) ^ dyadicDepth s *
          (endpointUpper * dualScale N s y) :=
        mul_le_mul_of_nonneg_right hpow
          (mul_nonneg (endpointConstants_pos s).2.1.le hends.1.le)
      _ = blockUpperMultiple s * dualScale N s y := by
        unfold blockUpperMultiple
        ring_nf

/-- The terminal scale lies in the sharper fixed interval based directly on
the derivative endpoints. -/
theorem terminalScale_deriv_comparable
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    endpointLower s * dualScale N s y ≤
        terminalScale (deriv f b) (deriv f a) ∧
      terminalScale (deriv f b) (deriv f a) ≤
        endpointUpper * dualScale N s y := by
  have hends := endpoint_derivative_bounds hN hs hy hP heps hf
  have hterminal := terminalScale_spec hends.2.2.1 hends.2.2.2.1
  exact ⟨hends.2.1.le.trans hterminal.2.1,
    hterminal.2.2.1.trans hends.2.2.2.2.le⟩

/-! ## Normalizing one block and the complete finite block sum -/

/-- Exact distributed normal form of `dualBlockUpperBound`. -/
theorem dualBlockUpperBound_eq_normalized
    {k l s y alpha : ℝ} (params : Parameters k l s)
    (hs : 0 < s) (hy : 0 < y) (hAlpha : 0 < alpha) (j : ℕ) :
    dualBlockUpperBound params y alpha j =
      params.pairConstant * dualSqrtFactor s *
        ((y ^ (1 / s)) ^ (k + 1 / 2) *
            (dyadicCut alpha j) ^ blockMainExponent k l s +
          (y ^ (1 / s)) ^ (-(1 : ℝ) / 2) *
            (dyadicCut alpha j) ^ blockErrorExponent s) := by
  have hJ : 0 < dyadicCut alpha j := dyadicCut_pos hAlpha j
  have heta : 0 < y ^ (1 / s) := Real.rpow_pos_of_pos hy _
  have hsigma : 0 < 1 / s := by positivity
  dsimp only [dualBlockUpperBound]
  let model : ℝ :=
    ((y ^ (1 / s) * dyadicCut alpha j ^ (-(1 / s))) ^ k *
        dyadicCut alpha j ^ l) +
      (y ^ (1 / s))⁻¹ * dyadicCut alpha j ^ (1 / s)
  have herr : (1 / s) / 2 = 1 / (2 * s) := by
    field_simp [hs.ne']
  change params.pairConstant * model *
      dualModelWeight (1 / s) (y ^ (1 / s)) (dyadicCut alpha j) = _
  calc
    params.pairConstant * model *
          dualModelWeight (1 / s) (y ^ (1 / s)) (dyadicCut alpha j) =
        params.pairConstant *
          (dualModelWeight (1 / s) (y ^ (1 / s)) (dyadicCut alpha j) * model) := by
      ring_nf
    _ = params.pairConstant *
        (Real.sqrt (5 / 4 * (1 / s)) *
          ((y ^ (1 / s)) ^ (k + 1 / 2) *
              (dyadicCut alpha j) ^
                (l - 1 / 2 - (k + 1 / 2) * (1 / s)) +
            (y ^ (1 / s)) ^ (-(1 : ℝ) / 2) *
              (dyadicCut alpha j) ^ (-(1 : ℝ) / 2 + (1 / s) / 2))) := by
      rw [show model =
          ((y ^ (1 / s) * dyadicCut alpha j ^ (-(1 / s))) ^ k *
              dyadicCut alpha j ^ l) +
            (y ^ (1 / s))⁻¹ * dyadicCut alpha j ^ (1 / s) by rfl,
        dualModelWeight_mul_model_eq hsigma heta hJ]
    _ = params.pairConstant * dualSqrtFactor s *
        ((y ^ (1 / s)) ^ (k + 1 / 2) *
            (dyadicCut alpha j) ^ blockMainExponent k l s +
          (y ^ (1 / s)) ^ (-(1 : ℝ) / 2) *
            (dyadicCut alpha j) ^ blockErrorExponent s) := by
      unfold dualSqrtFactor blockMainExponent blockErrorExponent
      rw [herr]
      ring_nf

/-- Normalize one explicit block model against the two global scales. -/
theorem dualBlockUpperBound_le_main_error
    {k l s N y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f)
    {j : ℕ} (hj : j < dyadicDepth s) :
    dualBlockUpperBound params y (deriv f b) j ≤
      params.pairConstant * dualSqrtFactor s *
        (blockMainRatio k l s *
            (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
          blockErrorRatio s * phaseScale N s y ^ (-(1 : ℝ) / 2)) := by
  have hends := endpoint_derivative_bounds hN hs hy hP heps hf
  have hcompare := dyadicCut_deriv_comparable hN hs hy hP heps hf hj
  have hmain := dual_block_main_scale_le hN hs hy
    (endpointConstants_pos s).1 (blockUpperMultiple_pos s)
    hcompare.1 hcompare.2 (k := k) (l := l)
  have herror := dual_block_error_scale_le hN hs hy
    (endpointConstants_pos s).1 (blockUpperMultiple_pos s)
    hcompare.1 hcompare.2
  rw [dualBlockUpperBound_eq_normalized params hs hy hends.2.2.1 j]
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add (by
      simpa only [blockMainRatio, blockMainExponent] using hmain) (by
      simpa only [blockErrorRatio, blockErrorExponent] using herror)
  · exact mul_nonneg params.pairConstant_nonneg (dualSqrtFactor_pos hs).le

/-- Sum the normalized one-block estimate over the fixed dyadic depth. -/
theorem sum_dualBlockUpperBounds_le_two_scales
    {k l s N y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    (∑ j ∈ Finset.range (dyadicDepth s),
        dualBlockUpperBound params y (deriv f b) j) ≤
      mainBoundMainCoefficient params *
          (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
        ((dyadicDepth s : ℝ) * params.pairConstant * dualSqrtFactor s *
            blockErrorRatio s) * phaseScale N s y ^ (-(1 : ℝ) / 2) := by
  calc
    (∑ j ∈ Finset.range (dyadicDepth s),
        dualBlockUpperBound params y (deriv f b) j) ≤
      ∑ _j ∈ Finset.range (dyadicDepth s),
        params.pairConstant * dualSqrtFactor s *
          (blockMainRatio k l s *
              (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
            blockErrorRatio s * phaseScale N s y ^ (-(1 : ℝ) / 2)) := by
      exact Finset.sum_le_sum fun j hj =>
        dualBlockUpperBound_le_main_error
          params hN hs hy hP heps hf (Finset.mem_range.mp hj)
    _ = mainBoundMainCoefficient params *
          (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
        ((dyadicDepth s : ℝ) * params.pairConstant * dualSqrtFactor s *
            blockErrorRatio s) * phaseScale N s y ^ (-(1 : ℝ) / 2) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      unfold mainBoundMainCoefficient
      ring_nf

/-! ## Normalizing the endpoint terms -/

/-- The two literal stationary endpoint costs are exactly a fixed multiple of
`F^(-1/2) N`. -/
theorem two_curvatureWeightBound_eq_largeErrorScale
    {N s y : ℝ} (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) :
    2 * curvatureWeightBound N s y =
      (2 * curvatureLower s ^ (-(1 : ℝ) / 2)) *
        (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
  rw [curvatureWeightBound_eq hN hs hy]
  ring_nf

/-- Normalize the terminal dual endpoint model using its sharper scale
comparison. -/
theorem terminal_dualModelWeight_le_largeErrorScale
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    dualModelWeight (1 / s) (y ^ (1 / s))
        (terminalScale (deriv f b) (deriv f a)) ≤
      (dualSqrtFactor s * terminalWeightRatio s) *
        (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
  have hcompare := terminalScale_deriv_comparable hN hs hy hP heps hf
  simpa only [terminalWeightRatio] using
    (dualModelWeight_le_largeErrorScale hN hs hy
      (endpointConstants_pos s).1 (endpointConstants_pos s).2.1
      hcompare.1 hcompare.2)

/-! ## The complete numerical main bound -/

/-- Normalize the complete right-hand side from `GKBProcessMainTerm` with
separate coefficients for the B-main and `F^(-1/2)N` scales.  This theorem is
strictly stronger than the single-constant form below. -/
theorem sum_dualBlockUpperBounds_add_endpoints_le_two_scales
    {k l s N y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 1 ≤ N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    (∑ j ∈ Finset.range (dyadicDepth s),
        dualBlockUpperBound params y (deriv f b) j) +
        2 * curvatureWeightBound N s y +
          dualModelWeight (1 / s) (y ^ (1 / s))
            (terminalScale (deriv f b) (deriv f a)) ≤
      mainBoundMainCoefficient params *
          (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
        mainBoundErrorCoefficient params *
          (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hblocks := sum_dualBlockUpperBounds_le_two_scales
    params hNpos hs hy hP heps hf
  have hcurv := two_curvatureWeightBound_eq_largeErrorScale hNpos hs hy
  have hterminal := terminal_dualModelWeight_le_largeErrorScale
    hNpos hs hy hP heps hf
  have hphase : 0 ≤ phaseScale N s y ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg (phaseScale_pos (s := s) hNpos hy).le _
  have hphaseN :
      phaseScale N s y ^ (-(1 : ℝ) / 2) ≤
        phaseScale N s y ^ (-(1 : ℝ) / 2) * N := by
    calc
      phaseScale N s y ^ (-(1 : ℝ) / 2) =
          phaseScale N s y ^ (-(1 : ℝ) / 2) * 1 := by ring_nf
      _ ≤ phaseScale N s y ^ (-(1 : ℝ) / 2) * N :=
        mul_le_mul_of_nonneg_left hN hphase
  calc
    (∑ j ∈ Finset.range (dyadicDepth s),
          dualBlockUpperBound params y (deriv f b) j) +
          2 * curvatureWeightBound N s y +
            dualModelWeight (1 / s) (y ^ (1 / s))
              (terminalScale (deriv f b) (deriv f a)) ≤
        (mainBoundMainCoefficient params *
            (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
          ((dyadicDepth s : ℝ) * params.pairConstant * dualSqrtFactor s *
            blockErrorRatio s) * phaseScale N s y ^ (-(1 : ℝ) / 2)) +
          (2 * curvatureLower s ^ (-(1 : ℝ) / 2)) *
            (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) +
          (dualSqrtFactor s * terminalWeightRatio s) *
            (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
      rw [hcurv]
      exact add_le_add (add_le_add hblocks le_rfl) hterminal
    _ ≤ mainBoundMainCoefficient params *
          (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
        (((dyadicDepth s : ℝ) * params.pairConstant * dualSqrtFactor s *
            blockErrorRatio s) *
            (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) +
          (2 * curvatureLower s ^ (-(1 : ℝ) / 2)) *
            (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) +
          (dualSqrtFactor s * terminalWeightRatio s) *
            (phaseScale N s y ^ (-(1 : ℝ) / 2) * N)) := by
      have hcoeff : 0 ≤ (dyadicDepth s : ℝ) * params.pairConstant *
          dualSqrtFactor s * blockErrorRatio s :=
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) params.pairConstant_nonneg)
            (dualSqrtFactor_pos hs).le)
          (blockErrorRatio_pos s).le
      have hscaled := mul_le_mul_of_nonneg_left hphaseN hcoeff
      calc
        mainBoundMainCoefficient params *
              (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
              ((dyadicDepth s : ℝ) * params.pairConstant * dualSqrtFactor s *
                blockErrorRatio s) * phaseScale N s y ^ (-(1 : ℝ) / 2) +
            (2 * curvatureLower s ^ (-(1 : ℝ) / 2)) *
              (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) +
            (dualSqrtFactor s * terminalWeightRatio s) *
              (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) ≤
          (mainBoundMainCoefficient params *
              (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
              ((dyadicDepth s : ℝ) * params.pairConstant * dualSqrtFactor s *
                blockErrorRatio s) *
                (phaseScale N s y ^ (-(1 : ℝ) / 2) * N)) +
            (2 * curvatureLower s ^ (-(1 : ℝ) / 2)) *
              (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) +
            (dualSqrtFactor s * terminalWeightRatio s) *
              (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) :=
          add_le_add (add_le_add (add_le_add le_rfl hscaled) le_rfl) le_rfl
        _ = mainBoundMainCoefficient params *
              (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
            (((dyadicDepth s : ℝ) * params.pairConstant * dualSqrtFactor s *
                blockErrorRatio s) *
                (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) +
              (2 * curvatureLower s ^ (-(1 : ℝ) / 2)) *
                (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) +
              (dualSqrtFactor s * terminalWeightRatio s) *
                (phaseScale N s y ^ (-(1 : ℝ) / 2) * N)) := by ring_nf
    _ = mainBoundMainCoefficient params *
          (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
        mainBoundErrorCoefficient params *
          (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
      unfold mainBoundErrorCoefficient
      ring_nf

/-- Single-constant form of the complete numerical normalization. -/
theorem sum_dualBlockUpperBounds_add_endpoints_le_mainBoundConstant
    {k l s N y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 1 ≤ N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    (∑ j ∈ Finset.range (dyadicDepth s),
        dualBlockUpperBound params y (deriv f b) j) +
        2 * curvatureWeightBound N s y +
          dualModelWeight (1 / s) (y ^ (1 / s))
            (terminalScale (deriv f b) (deriv f a)) ≤
      mainBoundConstant params *
        (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2) +
          phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
  have htwo := sum_dualBlockUpperBounds_add_endpoints_le_two_scales
    params hN hs hy hP heps hf
  have hmain : 0 ≤ dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by
    exact mul_nonneg
      (Real.rpow_nonneg (dualScale_pos (s := s) (zero_lt_one.trans_le hN) hy).le _)
      (Real.rpow_nonneg (zero_le_one.trans hN) _)
  have herror : 0 ≤ phaseScale N s y ^ (-(1 : ℝ) / 2) * N := by
    exact mul_nonneg
      (Real.rpow_nonneg (phaseScale_pos (s := s) (zero_lt_one.trans_le hN) hy).le _)
      (zero_le_one.trans hN)
  have hCmain := mainBoundMainCoefficient_nonneg params hs
  have hCerror := mainBoundErrorCoefficient_nonneg params hs
  apply htwo.trans
  calc
    mainBoundMainCoefficient params *
          (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
        mainBoundErrorCoefficient params *
          (phaseScale N s y ^ (-(1 : ℝ) / 2) * N) ≤
      mainBoundMainCoefficient params *
          (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2) +
            phaseScale N s y ^ (-(1 : ℝ) / 2) * N) +
        mainBoundErrorCoefficient params *
          (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2) +
            phaseScale N s y ^ (-(1 : ℝ) / 2) * N) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right herror) hCmain)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hmain) hCerror)
    _ = mainBoundConstant params *
        (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2) +
          phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
      unfold mainBoundConstant
      ring_nf

/-! ## Applying the numerical bound to the literal stationary sum -/

/-- Assembly-ready stationary-main-term bound with one fixed coefficient. -/
theorem lemma36_mainTerm_le_mainBoundConstant_mul
    {k l s N y a b : ℝ} {f x phi : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 1 ≤ N) (hs : 0 < s) (hy : 0 < y)
    (hf : InGKClass N params.originalOrder s y params.originalError a b f)
    (hab : a < b) (hphi : ContDiff ℝ params.originalOrder phi)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu)) :
    ‖∑ nu ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
        e (f (x (nu : ℝ)) - (nu : ℝ) * x (nu : ℝ) - 1 / 8) /
          ((Real.sqrt |iteratedDeriv 2 f (x (nu : ℝ))| : ℝ) : ℂ)‖ ≤
      mainBoundConstant params *
        (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2) +
          phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := by
  have hmainTerm := norm_lemma36_stationarySum_le_dyadicBlockUpperBounds
    params (zero_lt_one.trans_le hN) hs hy hf hab hphi hx hlegendre
  exact hmainTerm.trans
    (sum_dualBlockUpperBounds_add_endpoints_le_mainBoundConstant
      params hN hs hy params.four_le_originalOrder
        params.originalError_le_quarter hf)

/-- In the large-`L` regime the error scale is itself below the B-main scale,
so the complete stationary main term is bounded by a fixed multiple of that
single scale. -/
theorem lemma36_mainTerm_le_two_mul_mainBoundConstant_mul_bMain
    {k l s N y a b : ℝ} {f x phi : ℝ → ℝ}
    (params : Parameters k l s)
    (hN : 1 ≤ N) (hs : 0 < s) (hy : 0 < y)
    (hL : 1 ≤ dualScale N s y) (hk : 0 ≤ k) (hl : 1 / 2 ≤ l)
    (hf : InGKClass N params.originalOrder s y params.originalError a b f)
    (hab : a < b) (hphi : ContDiff ℝ params.originalOrder phi)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hlegendre : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu)) :
    ‖∑ nu ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
        e (f (x (nu : ℝ)) - (nu : ℝ) * x (nu : ℝ) - 1 / 8) /
          ((Real.sqrt |iteratedDeriv 2 f (x (nu : ℝ))| : ℝ) : ℂ)‖ ≤
      (2 * mainBoundConstant params) *
        (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by
  have hbase := lemma36_mainTerm_le_mainBoundConstant_mul
    params hN hs hy hf hab hphi hx hlegendre
  have herror := phaseScale_neg_half_mul_le_bMain hN hy hL hk hl
  have hC := mainBoundConstant_nonneg params hs
  calc
    ‖∑ nu ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
        e (f (x (nu : ℝ)) - (nu : ℝ) * x (nu : ℝ) - 1 / 8) /
          ((Real.sqrt |iteratedDeriv 2 f (x (nu : ℝ))| : ℝ) : ℂ)‖ ≤
      mainBoundConstant params *
        (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2) +
          phaseScale N s y ^ (-(1 : ℝ) / 2) * N) := hbase
    _ ≤ mainBoundConstant params *
        ((dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
          (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) hC
    _ = (2 * mainBoundConstant params) *
        (dualScale N s y ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by ring_nf

end GKB

end LeanProofs.IntegerPoints
