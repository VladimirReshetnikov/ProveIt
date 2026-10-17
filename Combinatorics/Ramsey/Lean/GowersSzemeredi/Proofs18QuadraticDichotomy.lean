import GowersSzemeredi.Proofs18QuadraticThresholdGrowth

/-! A fully quantified one-step alternative for progressions of length four.
Iteration between cyclic and interval models is not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A convenient explicit single-exponential sufficient modulus. -/
def quadraticExponentialThreshold (alpha : Real) : Real :=
  Real.exp ((4 + 6 * section5LocalRefinementConstant 2 1) *
    (2 / alpha) ^ (12380 * 2048 + 24744 : Nat))

/-- The density-increment conclusion under a single-exponential bound. -/
theorem quadratic_density_increment_of_exp_power
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N : Nat) [NeZero N] [Fact N.Prime] (hN : quadraticExponentialThreshold alpha ≤ N)
    (A : Finset (ZMod N)) (hnot : ¬ UniformSetOfDegree A alpha 2) :
    ∃ P : ModAP N, P.IsProper ∧
      quadraticDiscrepancyParameter alpha / 4 * (N : Real) ^ quadraticDiscrepancyExponent alpha ≤
        (P.carrier.card : Real) ∧
      (density A + quadraticDiscrepancyParameter alpha / 4) * P.carrier.card ≤ (A ∩ P.carrier).card := by
  exact quadratic_nonuniformity_density_increment_explicit alpha hα hαone N
    ((quadraticDensityThreshold_le_exp_power hα hαone).trans hN) A hnot

end LeanProofs.GowersSzemeredi
