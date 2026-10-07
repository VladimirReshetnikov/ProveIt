import GowersSzemeredi.Proofs18QuadraticDoubleExponential

/-! An explicit numerical upper bound on the fixed constants in the
four-term iteration, suitable for comparison with the Section 18 tower. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Only degrees one and two enter the quadratic refinement constants. -/
theorem section5_small_degree_refinement_constant_upper {k : Nat} (hk : k ≤ 2) :
    section5LocalRefinementConstant k 1 ≤ (2 : Real) ^ ((2 : Nat) ^ 321) + 4 := by
  have hK : polynomialPartitionConstant k ≤ 2048 := by
    interval_cases k <;> norm_num [polynomialPartitionConstant, Nat.factorial]
  have he : 40 * k ^ 3 + 1 ≤ 321 := by
    have hh := Nat.pow_le_pow_left hk 3
    norm_num at hh
    omega
  have hW : (polynomialPartitionThreshold k : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 321) := by
    simp only [polynomialPartitionThreshold, weylThreshold, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, ← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) he)
  have h8192 : 8192 ≤ (2 : Nat) ^ 321 :=
    (by norm_num : 8192 ≤ (2 : Nat) ^ 13).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h16 : (16 : Real) ^ polynomialPartitionConstant k ≤ (2 : Real) ^ ((2 : Nat) ^ 321) := by
    calc
      _ ≤ (16 : Real) ^ 2048 := pow_le_pow_right₀ (by norm_num) hK
      _ = (2 : Real) ^ 8192 := by rw [show (16 : Real) = 2 ^ (4 : Nat) by norm_num, ← pow_mul]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) h8192
  have hpi : (4 * Real.pi / 1) ^ polynomialPartitionConstant k ≤ (2 : Real) ^ ((2 : Nat) ^ 321) := by
    apply le_trans _ h16
    apply pow_le_pow_left₀ (by positivity)
    have hh := Real.pi_lt_four
    linarith
  unfold section5LocalRefinementConstant
  exact add_le_add_left (max_le (max_le hW hpi)
    ((pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 4) (by norm_num : (4 : Real) ≤ 16) _).trans h16)) 4

/-- The fixed prefactor is far below the exponent reserve in the source's
four-term instance of the quantitative Szemeredi threshold. -/
theorem quadraticIterationLogBudgetConstant_upper :
    quadraticIterationLogBudgetConstant + 1 ≤ (2 : Real) ^ ((2 : Nat) ^ 322) := by
  let W := (2 : Real) ^ ((2 : Nat) ^ 321)
  have h1 := section5_small_degree_refinement_constant_upper (k := 1) (by omega)
  have h2 := section5_small_degree_refinement_constant_upper (k := 2) (by omega)
  have hW : (8192 : Real) ≤ W := by
    exact (by norm_num : (8192 : Real) ≤ 2 ^ (13 : Nat)).trans
      (pow_le_pow_right₀ (by norm_num) (by
        exact (by norm_num : 13 ≤ (2 : Nat) ^ 4).trans (Nat.pow_le_pow_right (by norm_num) (by omega))))
  have hbound : quadraticIterationLogBudgetConstant + 1 ≤ 16 * W := by
    unfold quadraticIterationLogBudgetConstant
    dsimp [W] at hW ⊢
    linarith
  have hexp : (2 : Nat) ^ 321 + 4 ≤ 2 ^ 322 := by
    have hh : 4 ≤ (2 : Nat) ^ 321 :=
      (by norm_num : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show (322 : Nat) = 321 + 1 by omega, pow_succ]
    omega
  calc
    _ ≤ 16 * W := hbound
    _ = (2 : Real) ^ ((2 : Nat) ^ 321 + 4) := by
      rw [pow_add]
      dsimp [W]
      norm_num only [show (2 : Real) ^ (4 : Nat) = 16 by norm_num]
      ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hexp

end LeanProofs.GowersSzemeredi
