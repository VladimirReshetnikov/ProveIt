import GowersSzemeredi.Proofs18QuadraticThresholdGrowth

/-! A fully quantified one-step alternative for progressions of length four.
Iteration between cyclic and interval models is not asserted here.

`quadratic_density_increment_of_exp_power` is in
`Proofs18QuadraticDichotomySide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A convenient explicit single-exponential sufficient modulus. -/
def quadraticExponentialThreshold (alpha : Real) : Real :=
  Real.exp ((4 + 6 * section5LocalRefinementConstant 2 1) *
    (2 / alpha) ^ (12380 * 2048 + 24744 : Nat))

end LeanProofs.GowersSzemeredi
