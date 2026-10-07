import GowersSzemeredi.Proofs18FejerPrimeThresholdEnvelope

/-! Numerical bounds on the fixed constants used by cubic phase removal. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

set_option exponentiation.threshold 2048 in
/-- The fixed refinement constants through degree three have one explicit
numerical upper bound. No enormous natural outer power is evaluated. -/
theorem section5_degree_le_three_refinement_constant_upper {k : Nat} (hk : k ≤ 3) :
    section5LocalRefinementConstant k 1 ≤ (2 : Real) ^ ((2 : Nat) ^ 1082) := by
  let W := (2 : Real) ^ ((2 : Nat) ^ 1081)
  have hK : polynomialPartitionConstant k ≤ 2359296 := by
    interval_cases k <;> norm_num [polynomialPartitionConstant, Nat.factorial]
  have he : 40 * k ^ 3 + 1 ≤ 1081 := by
    have hh := Nat.pow_le_pow_left hk 3
    norm_num at hh
    omega
  have hW : (polynomialPartitionThreshold k : Real) ≤ W := by
    simp only [polynomialPartitionThreshold, weylThreshold, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, ← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) he)
  have h16 : (16 : Real) ^ polynomialPartitionConstant k ≤ W := by
    calc
      _ ≤ (16 : Real) ^ (2359296 : Nat) := pow_le_pow_right₀ (by norm_num) hK
      _ = (2 : Real) ^ (9437184 : Nat) := by
        rw [show (16 : Real) = 2 ^ (4 : Nat) by norm_num, ← pow_mul]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num : (9437184 : Nat) ≤ (2 : Nat) ^ 1081)
  have hpi : (4 * Real.pi / 1) ^ polynomialPartitionConstant k ≤ W := by
    apply le_trans _ h16
    apply pow_le_pow_left₀ (by positivity)
    have hp := Real.pi_lt_four
    linarith only [hp]
  have hmax : section5LocalRefinementConstant k 1 ≤ W + 4 := by
    unfold section5LocalRefinementConstant
    exact add_le_add (max_le (max_le hW hpi)
      ((pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 4) (by norm_num : (4 : Real) ≤ 16) _).trans h16)) le_rfl
  have h4 : (4 : Real) ≤ W := by
    calc
      _ = (2 : Real) ^ (2 : Nat) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num : (2 : Nat) ≤ (2 : Nat) ^ 1081)
  calc
    _ ≤ W + 4 := hmax
    _ ≤ W + W := add_le_add le_rfl h4
    _ = (2 : Real) ^ ((2 : Nat) ^ 1081 + 1) := by rw [pow_succ']; ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num : (2 : Nat) ^ 1081 + 1 ≤ (2 : Nat) ^ 1082)

set_option exponentiation.threshold 2048 in
/-- The fixed boundary refinement used by each quadratic model is covered
by the same numerical reserve, with one extra unit in the tower exponent. -/
theorem cubic_boundary_refinement_constant_upper :
    boundaryRefinementConstant (1 / 16) ≤ (2 : Real) ^ ((2 : Nat) ^ 1083) := by
  let eta := 4 * Real.pi * (1 / 16 : Real)
  have hη : 0 < eta := by dsimp [eta]; positivity
  have hηlow : (1 / 4 : Real) ≤ eta := by
    have hp := Real.pi_gt_three
    dsimp [eta]
    linarith only [hp]
  have hi : eta⁻¹ ≤ 4 := by
    have h := inv_anti₀ (by norm_num : (0 : Real) < 1 / 4) hηlow
    norm_num at h
    exact h
  have h := section5LocalRefinementConstant_le_scaled 1 eta 4 hη (by norm_num) hi
  have hK : polynomialPartitionConstant 1 = 16 := by norm_num [polynomialPartitionConstant, Nat.factorial]
  rw [hK] at h
  calc
    _ ≤ section5LocalRefinementConstant 1 1 * (4 : Real) ^ (16 : Nat) := h
    _ ≤ (2 : Real) ^ ((2 : Nat) ^ 1082) * (2 : Real) ^ (32 : Nat) := by
      apply mul_le_mul (section5_degree_le_three_refinement_constant_upper (by omega))
        (le_of_eq (by norm_num)) (by positivity) (by positivity)
    _ = (2 : Real) ^ ((2 : Nat) ^ 1082 + 32) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num : (2 : Nat) ^ 1082 + 32 ≤ (2 : Nat) ^ 1083)

set_option exponentiation.threshold 2048 in
/-- The count constant before phase removal is bounded uniformly in alpha. -/
theorem fejerCubicTwistedCountConstant_upper {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    fejerCubicTwistedCountConstant alpha ≤ (2 : Real) ^ ((2 : Nat) ^ 1084) := by
  let t := fejerCubicLocalCountExponent alpha
  let C := boundaryRefinementConstant (1 / 16)
  have ht : 0 < t := (fejerCubicLocalCountExponent_bounds hα hαone).1
  have ht1 : t ≤ 1 := (fejerCubicLocalCountExponent_bounds hα hαone).2
  have hC : 4 ≤ C := section5LocalRefinementConstant_ge_four 1 _
  have hC0 : 0 ≤ C := by linarith only [hC]
  have h8 : (8 : Real) ^ (1 - t) ≤ 8 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : Real) ≤ 8) (by linarith only [ht] : 1 - t ≤ 1)
  have h12 : (12 : Real) ^ t ≤ 12 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 12) ht1
  have hD : fejerCubicLocalCountConstant alpha ≤ 16 * C := by
    unfold fejerCubicLocalCountConstant
    apply max_le (by linarith only [hC])
    have h := mul_le_mul_of_nonneg_left h8 (show 0 ≤ 2 * C by positivity)
    nlinarith only [h]
  calc
    _ ≤ (16 * C) * 12 := mul_le_mul hD h12 (by positivity) (by positivity)
    _ ≤ (2 : Real) ^ (8 : Nat) * C := by norm_num; nlinarith only [hC0]
    _ ≤ (2 : Real) ^ (8 : Nat) * (2 : Real) ^ ((2 : Nat) ^ 1083) :=
      mul_le_mul_of_nonneg_left cubic_boundary_refinement_constant_upper (by positivity)
    _ = (2 : Real) ^ (8 + (2 : Nat) ^ 1083) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num : 8 + (2 : Nat) ^ 1083 ≤ (2 : Nat) ^ 1084)

end LeanProofs.GowersSzemeredi
