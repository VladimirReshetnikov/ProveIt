import GowersSzemeredi.Proofs18LengthSixThresholds
import GowersSzemeredi.Proofs18CubicRefinementConstantBounds
import GowersSzemeredi.Proofs05RefinementConstantBounds
import GowersSzemeredi.Proofs18LogarithmicPowerEnvelope
import GowersSzemeredi.Proofs18DoubleExponentialBounds

/-! The exponent and threshold of the length-six discrepancy bound.

`length_six_function_discrepancy` gives `FunctionDiscrepancyBound 4 α β σ T`
at explicit `σ = lsSigma` and `T = lsThreshold`. With `X = 2/α ≥ 2^700`
and recurrence constants `K₁, p₁, K₂, p₂ ≤ X³`:
* `lsSigma_inv_le : σ⁻¹ ≤ exp(X^(2^664 + 2))`. The cubic Fejér exponent
  is exponentially small in its input `y = η/(2·10⁵)`, and `2/y ≤ X^(2^603)`.
* `lsThreshold_le : T ≤ exp(exp(X^(2^700)))`. The double exponential comes
  from the cubic inverse threshold and from the phase-refinement constant
  raised to `1/σ`.

The fixed constants are absorbed by `X ≥ 2^700`:
* the degree-four refinement constant `section5LocalRefinementConstant 4 1`
  is `≤ 2^(2^2562) ≤ exp(X^4)`, because the Weyl threshold is
  `2^(2^(40·4³))`;
* the boundary constant is `≤ 2^(2^1083) ≤ exp(X^2)`. -/
set_option autoImplicit false
set_option exponentiation.threshold 4096
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The fixed constants -/

/-- The refinement constant in degree at most four is at most `2^(2^2562)`.
The degree stays a variable: with a literal degree, `simp` evaluates the
Weyl exponent `2^(40·4³)` to a numeral and the power calculus stalls. -/
theorem section5_degree_le_four_refinement_constant_upper {k : Nat} (hk : k ≤ 4) :
    section5LocalRefinementConstant k 1 ≤ (2 : Real) ^ ((2 : Nat) ^ 2562) := by
  let W := (2 : Real) ^ ((2 : Nat) ^ 2561)
  have hK : polynomialPartitionConstant k ≤ 2 ^ 35 := by
    interval_cases k <;> norm_num [polynomialPartitionConstant, Nat.factorial]
  have he : 40 * k ^ 3 + 1 ≤ 2561 := by
    have hh := Nat.pow_le_pow_left hk 3
    norm_num at hh
    omega
  have hW : (polynomialPartitionThreshold k : Real) ≤ W := by
    simp only [polynomialPartitionThreshold, weylThreshold, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, ← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) he)
  have h16 : (16 : Real) ^ polynomialPartitionConstant k ≤ W := by
    calc
      _ ≤ (16 : Real) ^ ((2 : Nat) ^ 35) := pow_le_pow_right₀ (by norm_num) hK
      _ = (2 : Real) ^ (4 * (2 : Nat) ^ 35) := by
        rw [show (16 : Real) = 2 ^ (4 : Nat) by norm_num, ← pow_mul]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hpi : (4 * Real.pi / 1) ^ polynomialPartitionConstant k ≤ W := by
    apply le_trans _ h16
    apply pow_le_pow_left₀ (by positivity)
    have hp := Real.pi_lt_four
    linarith only [hp]
  have hmax : section5LocalRefinementConstant k 1 ≤ W + 4 := by
    unfold section5LocalRefinementConstant
    exact add_le_add (max_le (max_le hW hpi)
      ((pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 4) (by norm_num : (4 : Real) ≤ 16) _).trans
        h16)) le_rfl
  have h4 : (4 : Real) ≤ W := by
    calc
      _ = (2 : Real) ^ (2 : Nat) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num : (2 : Nat) ≤ (2 : Nat) ^ 2561)
  calc
    _ ≤ W + 4 := hmax
    _ ≤ W + W := add_le_add le_rfl h4
    _ = (2 : Real) ^ ((2 : Nat) ^ 2561 + 1) := by rw [pow_succ, ← two_mul, mul_comm]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- `2^n ≤ exp(X^j)` once `n ≤ (2^700)^j ≤ X^j`. -/
theorem two_pow_le_exp_of_large {X : Real} {n j : Nat} (hX : (2 : Real) ^ 700 ≤ X)
    (hn : n ≤ 700 * j) : (2 : Real) ^ ((2 : Nat) ^ n) ≤ Real.exp (X ^ j) := by
  have he2 : (2 : Real) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : Real); linarith only [this]
  have h1 : (2 : Real) ^ ((2 : Nat) ^ n) ≤ Real.exp (((2 : Nat) ^ n : Nat) : Real) := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) he2 _
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  push_cast
  calc (2 : Real) ^ n ≤ (2 : Real) ^ (700 * j) := pow_le_pow_right₀ (by norm_num) hn
    _ = ((2 : Real) ^ 700) ^ j := pow_mul _ _ _
    _ ≤ X ^ j := pow_le_pow_left₀ (by positivity) hX j

theorem section5_four_le_exp {X : Real} (hX : (2 : Real) ^ 700 ≤ X) :
    section5LocalRefinementConstant 4 1 ≤ Real.exp (X ^ 4) :=
  (section5_degree_le_four_refinement_constant_upper le_rfl).trans (two_pow_le_exp_of_large hX (by norm_num))

theorem boundary_sixteenth_le_exp {X : Real} (hX : (2 : Real) ^ 700 ≤ X) :
    boundaryRefinementConstant (1 / 16) ≤ Real.exp (X ^ 2) :=
  cubic_boundary_refinement_constant_upper.trans (two_pow_le_exp_of_large hX (by norm_num))

/-! ### The cubic input and the exponent `σ` -/

/-- The cubic input `y = η/(2·10⁵)` of the length-six route. -/
def lsY (alpha : Real) : Real := singlePieceCubicInput sixQb (sixC sixQb alpha) alpha

/-- The cubic exponent `σ₃ = min (fejerCubicDiscrepancyExponent y) 16`. -/
def lsSigma3 (alpha : Real) : Real := min (fejerCubicDiscrepancyExponent (lsY alpha)) 16

/-- The exponent `σ` of the length-six discrepancy bound. -/
def lsSigma (K1 p1 p2 : Nat) (alpha : Real) : Real :=
  inverseStepExponent (2 + 1) (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha)
    (lsSigma3 alpha)

theorem lsSigma3_bounds {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < lsSigma3 alpha ∧ lsSigma3 alpha ≤ 16 ∧
      (lsSigma3 alpha)⁻¹ ≤ Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 664)) := by
  obtain ⟨y0, y1, yi⟩ := lsCubicInput_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hf0 := fejerCubicDiscrepancyExponent_pos y0 y1
  have hfi := fejerCubicDiscrepancyExponent_inv_le_exp y0 y1
  have hYp : (2 / singlePieceCubicInput sixQb (sixC sixQb alpha) alpha) ^ ((2 : Nat) ^ 61) ≤
      (2 / alpha) ^ ((2 : Nat) ^ 664) := by
    have h := pow_le_pow_left₀ (div_pos (by norm_num) y0).le yi ((2 : Nat) ^ 61)
    rw [← pow_mul] at h
    exact h.trans (pow_le_pow_right₀ hX1 (by norm_num))
  unfold lsSigma3 lsY
  refine ⟨lt_min hf0 (by norm_num), min_le_right _ _, ?_⟩
  rcases min_choice (fejerCubicDiscrepancyExponent (singlePieceCubicInput sixQb (sixC sixQb alpha)
    alpha)) 16 with h | h
  · rw [h]; exact hfi.trans (Real.exp_le_exp.mpr hYp)
  · rw [h]
    exact (show ((16 : Real))⁻¹ ≤ 1 by norm_num).trans (Real.one_le_exp_iff.mpr (by positivity))

theorem lsSigma_inv_le {K1 p1 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) (hp2 : 0 < p2)
    {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3)
    (hq : (p2 : Real) ≤ (2 / alpha) ^ 3) :
    0 < lsSigma K1 p1 p2 alpha ∧
      (lsSigma K1 p1 p2 alpha)⁻¹ ≤ Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 664 + 2)) := by
  obtain ⟨e0, ei⟩ := lsE_inv_le_power hK1 hp1 hp2 ha ha2 hK hp hq
  obtain ⟨s0, -, si⟩ := lsSigma3_bounds ha ha2
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hP : (polynomialPartitionConstant (2 + 1 + 1) : Real) ≤ 2 ^ 35 := by
    norm_num [polynomialPartitionConstant, Nat.factorial]
  have hP0 : (0 : Real) < polynomialPartitionConstant (2 + 1 + 1) := by
    norm_num [polynomialPartitionConstant, Nat.factorial]
  unfold lsSigma inverseStepExponent phaseInverseExponent
  set E := lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha
  set s := lsSigma3 alpha
  set P := (polynomialPartitionConstant (2 + 1 + 1) : Real)
  set X := 2 / alpha with hX
  clear_value E s P X
  refine ⟨by positivity, ?_⟩
  rw [show (E * (s / 16) / (2 * P))⁻¹ = 32 * P * E⁻¹ * s⁻¹ by field_simp; ring]
  have hc : 32 * P ≤ Real.exp (X ^ ((2 : Nat) ^ 664)) :=
    (const_le_exp_pow (j := 40) hX2 (by nlinarith only [hP])).trans (exp_pow_mono hX2 (by norm_num))
  have hEe : E⁻¹ ≤ Real.exp (X ^ ((2 : Nat) ^ 664)) :=
    le_exp_pow_of_le_pow (ei.trans (pow_le_pow_right₀ (le_trans (by norm_num) hX2) (by norm_num)))
  have h1 := exp_mul_le hX2 (inv_pos.mpr e0).le hc hEe
  exact exp_mul_le hX2 (inv_pos.mpr s0).le h1 (si.trans (exp_pow_mono hX2 (by norm_num)))

/-! ### The threshold `T` -/

/-- The threshold `T` of the length-six discrepancy bound. -/
def lsThreshold (K1 p1 K2 p2 : Nat) (alpha : Real) : Real :=
  max (shortLocalizationThreshold (2 + 1)
      (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha) (6 * ((2 + 1 : Nat) : Real))
      (fejerCubicInverseThreshold (lsY alpha))
      (lsTloc (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) K2 p2 alpha))
    (inverseStepThreshold (2 + 1) (singlePieceEta sixQb (sixC sixQb alpha) alpha 2)
      (fejerCubicDiscrepancyParameter (lsY alpha))
      (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha)
      (6 * ((2 + 1 : Nat) : Real)) (lsSigma3 alpha))

/-- The short-localization part of `T` is double exponential. -/
theorem lsShortThreshold_le {K1 p1 K2 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) (hK2 : 0 < K2)
    (hp2 : 0 < p2) {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3)
    (hK' : (K2 : Real) ≤ (2 / alpha) ^ 3) (hp' : (p2 : Real) ≤ (2 / alpha) ^ 3) :
    shortLocalizationThreshold (2 + 1)
        (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha) (6 * ((2 + 1 : Nat) : Real))
        (fejerCubicInverseThreshold (lsY alpha))
        (lsTloc (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) K2 p2 alpha) ≤
      Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 665 + 2))) := by
  obtain ⟨y0, y1, yi⟩ := lsCubicInput_bounds ha ha2
  obtain ⟨e0, ei⟩ := lsE_inv_le_power hK1 hp1 hp2 ha ha2 hK hp hp'
  have hTl := lsTloc_le_exp hK1 hp1 hK2 hp2 ha ha2 hK hp hK' hp'
  have hT3 : fejerCubicInverseThreshold (lsY alpha) ≤
      Real.exp (Real.exp ((2 / lsY alpha) ^ ((2 : Nat) ^ 62))) :=
    fejerCubicInverseThreshold_le_double_exp y0 y1
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hYp : (2 / lsY alpha) ^ ((2 : Nat) ^ 62) ≤ (2 / alpha) ^ ((2 : Nat) ^ 665) := by
    have h := pow_le_pow_left₀ (div_pos (by norm_num) y0).le yi ((2 : Nat) ^ 62)
    rw [← pow_mul] at h
    exact h.trans (pow_le_pow_right₀ hX1 (by norm_num))
  unfold shortLocalizationThreshold
  set E := lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha
  set T3 := fejerCubicInverseThreshold (lsY alpha)
  set Tl := lsTloc (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) K2 p2 alpha
  set X := 2 / alpha with hX
  clear_value E T3 Tl X
  have hT3' : T3 ≤ Real.exp (Real.exp (X ^ ((2 : Nat) ^ 665))) :=
    hT3.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hYp))
  have hsmall : ∀ c : Real, c ≤ 2 ^ 5 → c ≤ Real.exp (Real.exp (X ^ ((2 : Nat) ^ 665))) := by
    intro c hc
    exact le_exp_exp_of_le_exp ((const_le_exp_pow hX2 hc).trans (exp_pow_mono hX2 (by norm_num)))
  have hC : 6 * ((2 + 1 : Nat) : Real) * max 2 T3 ≤
      Real.exp (Real.exp (X ^ ((2 : Nat) ^ 665) + 1)) :=
    (mul_le_mul (hsmall _ (by norm_num)) (max_le (hsmall _ (by norm_num)) hT3')
      (le_trans (by norm_num) (le_max_left _ _)) (Real.exp_pos _).le).trans exp_exp_sq_le
  have hEi : E⁻¹ ≤ Real.exp (X ^ ((2 : Nat) ^ 643)) := le_exp_pow_of_le_pow ei
  have hP := positivePowerThreshold_one_le_double_exp e0.le hC hEi
  have hsum : X ^ ((2 : Nat) ^ 665) + 1 + X ^ ((2 : Nat) ^ 643) ≤ X ^ ((2 : Nat) ^ 665 + 2) := by
    have h1 : (1 : Real) ≤ X ^ ((2 : Nat) ^ 643) := one_le_pow_of_two_le hX2 _
    have h2 := pow_add_pow_le hX2 (show (2 : Nat) ^ 643 ≤ (2 : Nat) ^ 665 by norm_num)
    have h3 := pow_add_pow_le hX2 (show (2 : Nat) ^ 643 ≤ (2 : Nat) ^ 665 + 1 by norm_num)
    have h4 := pow_le_pow_right₀ (le_trans (by norm_num) hX2)
      (show (2 : Nat) ^ 643 ≤ (2 : Nat) ^ 665 by norm_num)
    linarith only [h1, h2, h3, h4]
  have hP' := hP.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hsum))
  have hmono : Real.exp (Real.exp (X ^ ((2 : Nat) ^ 665))) ≤
      Real.exp (Real.exp (X ^ ((2 : Nat) ^ 665 + 2))) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (le_trans (by norm_num) hX2) (by norm_num)))
  apply max_le (le_exp_exp_of_le_exp (hTl.trans (exp_pow_mono hX2 (by norm_num))))
  exact max_le ((hsmall _ (by norm_num)).trans hmono) hP'

/-- The phase-refinement part of `T` is double exponential. -/
theorem lsInverseThreshold_le {K1 p1 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) (hp2 : 0 < p2)
    {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) (hXbig : (2 : Real) ^ 700 ≤ 2 / alpha)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3)
    (hp' : (p2 : Real) ≤ (2 / alpha) ^ 3) :
    inverseStepThreshold (2 + 1) (singlePieceEta sixQb (sixC sixQb alpha) alpha 2)
        (fejerCubicDiscrepancyParameter (lsY alpha))
        (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha)
        (6 * ((2 + 1 : Nat) : Real)) (lsSigma3 alpha) ≤
      Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 699 + 3))) := by
  obtain ⟨y0, y1, yi⟩ := lsCubicInput_bounds ha ha2
  obtain ⟨n0, n1, ni⟩ := lsEta_bounds ha ha2
  obtain ⟨s0, s1, -⟩ := lsSigma3_bounds ha ha2
  obtain ⟨g0, gi⟩ := lsSigma_inv_le hK1 hp1 hp2 ha ha2 hK hp hp'
  have hb0 : 0 < fejerCubicDiscrepancyParameter (lsY alpha) :=
    fejerCubicDiscrepancyParameter_pos y0
  have hb1 : fejerCubicDiscrepancyParameter (lsY alpha) ≤ 1 :=
    fejerCubicDiscrepancyParameter_le_one y0 y1
  have hbi : (fejerCubicDiscrepancyParameter (lsY alpha) / 8)⁻¹ ≤
      (2 / lsY alpha) ^ ((2 : Nat) ^ 60) := fejer_cubic_gain_inv_le_power y0 y1
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX2 : 2 ≤ 2 / alpha := by linarith only [hX4]
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  have hX0 : 0 ≤ 2 / alpha := by linarith only [hX4]
  have hR4 := section5_four_le_exp hXbig
  have hBd := boundary_sixteenth_le_exp hXbig
  have hYp : (2 / lsY alpha) ^ ((2 : Nat) ^ 60) ≤ (2 / alpha) ^ ((2 : Nat) ^ 663) := by
    have h := pow_le_pow_left₀ (div_pos (by norm_num) y0).le yi ((2 : Nat) ^ 60)
    rw [← pow_mul] at h
    exact h
  have hP1 : (1 : Real) ≤ polynomialPartitionConstant (2 + 1 + 1) := by
    norm_num [polynomialPartitionConstant, Nat.factorial]
  have hPn : polynomialPartitionConstant (2 + 1 + 1) ≤ 2 ^ 35 := by
    norm_num [polynomialPartitionConstant, Nat.factorial]
  unfold inverseStepThreshold phaseInverseConstant inverseStepCountConstant
  rw [show inverseStepExponent (2 + 1)
      (lsE (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) p2 alpha) (lsSigma3 alpha) =
      lsSigma K1 p1 p2 alpha from rfl]
  set b3 := fejerCubicDiscrepancyParameter (lsY alpha)
  set eta := singlePieceEta sixQb (sixC sixQb alpha) alpha 2
  set s3 := lsSigma3 alpha
  set sg := lsSigma K1 p1 p2 alpha
  set P := polynomialPartitionConstant (2 + 1 + 1)
  set X := 2 / alpha with hX
  clear_value b3 eta s3 sg X
  -- the refinement constant at `b = η β₃ / 2`
  have hb : 0 < eta * b3 / 2 := by positivity
  have hb1' : eta * b3 / 2 ≤ 1 := by
    have : eta * b3 ≤ 1 := mul_le_one₀ n1 hb0.le hb1
    linarith only [this]
  have hbinv : (eta * b3 / 2)⁻¹ ≤ X ^ ((2 : Nat) ^ 664) := by
    have hb3i : b3⁻¹ ≤ X ^ ((2 : Nat) ^ 663) := by
      have h8 : b3⁻¹ ≤ (b3 / 8)⁻¹ := inv_anti₀ (by positivity) (by linarith only [hb0])
      exact h8.trans (hbi.trans hYp)
    rw [show (eta * b3 / 2)⁻¹ = 2 * (eta⁻¹ * b3⁻¹) by field_simp]
    have h := mul_le_pow_add (inv_pos.mpr hb0).le ni hb3i hX0
    have h2 : 2 * (eta⁻¹ * b3⁻¹) ≤ X ^ (1 + ((2 : Nat) ^ 602 + (2 : Nat) ^ 663)) := by
      rw [pow_add, pow_one]; exact mul_le_mul hX2 h (by positivity) hX0
    exact h2.trans (pow_le_pow_right₀ hX1 (by norm_num))
  have hbT : 1 ≤ (eta * b3 / 2)⁻¹ := (one_le_inv₀ hb).mpr hb1'
  have hscaled := section5LocalRefinementConstant_le_scaled (2 + 1 + 1) (eta * b3 / 2)
    (eta * b3 / 2)⁻¹ hb hbT le_rfl
  have hpowP : (eta * b3 / 2)⁻¹ ^ P ≤ Real.exp (X ^ ((2 : Nat) ^ 699)) := by
    refine le_exp_pow_of_le_pow ((pow_le_pow_right₀ hbT hPn).trans ?_)
    calc (eta * b3 / 2)⁻¹ ^ ((2 : Nat) ^ 35) ≤ (X ^ ((2 : Nat) ^ 664)) ^ ((2 : Nat) ^ 35) :=
          pow_le_pow_left₀ (inv_pos.mpr hb).le hbinv _
      _ = X ^ ((2 : Nat) ^ 699) := by rw [← pow_mul]; norm_num
  have hR : section5LocalRefinementConstant (2 + 1 + 1) (eta * b3 / 2) ≤
      Real.exp (X ^ ((2 : Nat) ^ 699 + 1)) :=
    hscaled.trans (exp_mul_le hX2 (by positivity) (hR4.trans (exp_pow_mono hX2 (by norm_num)))
      hpowP)
  -- the count constant `D`
  have hs16 : s3 / 16 ≤ 1 := by linarith only [s1]
  have hs16' : 0 ≤ s3 / 16 := by positivity
  have h10 : (2 * ((2 + 1 + 2 : Nat) : Real)) ^ (1 - s3 / 16) ≤ 10 := by
    calc (2 * ((2 + 1 + 2 : Nat) : Real)) ^ (1 - s3 / 16) ≤
          (2 * ((2 + 1 + 2 : Nat) : Real)) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hs16'])
      _ = 10 := by norm_num
  have h18 : (6 * ((2 + 1 : Nat) : Real)) ^ (s3 / 16) ≤ 18 := by
    calc (6 * ((2 + 1 : Nat) : Real)) ^ (s3 / 16) ≤ (6 * ((2 + 1 : Nat) : Real)) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hs16
      _ = 18 := by norm_num
  have h18' : 1 ≤ (6 * ((2 + 1 : Nat) : Real)) ^ (s3 / 16) := Real.one_le_rpow (by norm_num) hs16'
  have hXX : (2 : Real) ^ 700 ≤ X ^ 2 := hXbig.trans (le_self_pow₀ hX1 (by norm_num))
  have h20e : (20 : Real) ≤ Real.exp (X ^ 2) :=
    le_exp_pow_of_le_pow ((show (20 : Real) ≤ 2 ^ 700 by norm_num).trans hXX)
  have hL : localInverseAssemblyConstant (2 * ((2 + 1 + 2 : Nat) : Real)) s3 ≤
      Real.exp (X ^ (2 + 1)) := by
    unfold localInverseAssemblyConstant
    apply max_le (Real.one_le_exp_iff.mpr (by positivity))
    have hB0 : 0 ≤ boundaryRefinementConstant (1 / 16) :=
      (section5LocalRefinementConstant_pos _ _).le
    have h20 : 2 * boundaryRefinementConstant (1 / 16) *
        (2 * ((2 + 1 + 2 : Nat) : Real)) ^ (1 - s3 / 16) ≤
        20 * boundaryRefinementConstant (1 / 16) := by
      have := mul_le_mul_of_nonneg_left h10
        (by positivity : (0 : Real) ≤ 2 * boundaryRefinementConstant (1 / 16))
      linarith only [this]
    exact h20.trans (exp_mul_le hX2 hB0 h20e hBd)
  have hL1 : 1 ≤ localInverseAssemblyConstant (2 * ((2 + 1 + 2 : Nat) : Real)) s3 := by
    unfold localInverseAssemblyConstant; exact le_max_left _ _
  have h18e : (6 * ((2 + 1 : Nat) : Real)) ^ (s3 / 16) ≤ Real.exp (X ^ (2 + 1)) :=
    h18.trans ((show (18 : Real) ≤ 20 by norm_num).trans (h20e.trans (exp_pow_mono hX2 (by norm_num))))
  have hD := exp_mul_le hX2 (Real.rpow_nonneg (by norm_num) _) hL h18e
  have hD1 : 1 ≤ localInverseAssemblyConstant (2 * ((2 + 1 + 2 : Nat) : Real)) s3 *
      (6 * ((2 + 1 : Nat) : Real)) ^ (s3 / 16) := one_le_mul_of_one_le_of_one_le hL1 h18'
  have hDp : (localInverseAssemblyConstant (2 * ((2 + 1 + 2 : Nat) : Real)) s3 *
      (6 * ((2 + 1 : Nat) : Real)) ^ (s3 / 16)) ^ ((P : Real))⁻¹ ≤
      localInverseAssemblyConstant (2 * ((2 + 1 + 2 : Nat) : Real)) s3 *
        (6 * ((2 + 1 : Nat) : Real)) ^ (s3 / 16) := by
    calc _ ≤ (localInverseAssemblyConstant (2 * ((2 + 1 + 2 : Nat) : Real)) s3 *
          (6 * ((2 + 1 : Nat) : Real)) ^ (s3 / 16)) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hD1 (inv_le_one_of_one_le₀ hP1)
      _ = _ := Real.rpow_one _
  have hPIC := exp_mul_le hX2 (Real.rpow_nonneg (by positivity) _) hR
    ((hDp.trans hD).trans (exp_pow_mono hX2 (by norm_num)))
  have hppt := positivePowerThreshold_one_le_double_exp g0.le (le_exp_exp_of_le_exp hPIC) gi
  refine hppt.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr ?_))
  exact pow_add_pow_le hX2 (by norm_num)

/-- **The threshold of the length-six bound is double exponential**:
`T ≤ exp(exp((2/α)^(2^700)))`. -/
theorem lsThreshold_le {K1 p1 K2 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1) (hK2 : 0 < K2)
    (hp2 : 0 < p2) {alpha : Real} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hXbig : (2 : Real) ^ 700 ≤ 2 / alpha)
    (hK : (K1 : Real) ≤ (2 / alpha) ^ 3) (hp : (p1 : Real) ≤ (2 / alpha) ^ 3)
    (hK' : (K2 : Real) ≤ (2 / alpha) ^ 3) (hp' : (p2 : Real) ≤ (2 / alpha) ^ 3) :
    lsThreshold K1 p1 K2 p2 alpha ≤ Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 700))) := by
  have hX4 := two_div_alpha_ge_four ha ha2
  have hX1 : 1 ≤ 2 / alpha := by linarith only [hX4]
  unfold lsThreshold
  apply max_le
  · exact (lsShortThreshold_le hK1 hp1 hK2 hp2 ha ha2 hK hp hK' hp').trans
      (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (pow_le_pow_right₀ hX1 (by norm_num))))
  · exact (lsInverseThreshold_le hK1 hp1 hp2 ha ha2 hXbig hK hp hp').trans
      (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (pow_le_pow_right₀ hX1 (by norm_num))))


end LeanProofs.GowersSzemeredi
