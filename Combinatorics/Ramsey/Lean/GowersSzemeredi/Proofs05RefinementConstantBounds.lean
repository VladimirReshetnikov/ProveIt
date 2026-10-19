import GowersSzemeredi.Proofs05Downstream

/-! Polynomial dependence of the phase-refinement constant on inverse error. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- An upper bound T on inverse error costs at most T^K in the local
refinement constant, where K is the polynomial partition exponent constant. -/
theorem section5LocalRefinementConstant_le_scaled (k : Nat) (eta T : Real)
    (hη : 0 < eta) (hT : 1 ≤ T) (heta : eta⁻¹ ≤ T) :
    section5LocalRefinementConstant k eta ≤
      section5LocalRefinementConstant k 1 * T ^ polynomialPartitionConstant k := by
  have hpow : 1 ≤ T ^ polynomialPartitionConstant k := one_le_pow₀ hT
  have hle (x : Real) (hx : 0 ≤ x) : x ≤ x * T ^ polynomialPartitionConstant k :=
    le_mul_of_one_le_right hx hpow
  have hphase : (4 * Real.pi / eta) ^ polynomialPartitionConstant k ≤
      (4 * Real.pi / 1) ^ polynomialPartitionConstant k * T ^ polynomialPartitionConstant k := by
    rw [div_one, ← mul_pow, div_eq_mul_inv]
    gcongr
  unfold section5LocalRefinementConstant
  rw [add_mul, max_mul_of_nonneg _ _ (zero_le_one.trans hpow),
    max_mul_of_nonneg _ _ (zero_le_one.trans hpow)]
  exact add_le_add (max_le_max (max_le_max (hle _ (by positivity)) hphase)
    (hle _ (by positivity))) (hle 4 (by norm_num))

end LeanProofs.GowersSzemeredi
