import GowersSzemeredi.Proofs18FejerCubicParameters

/-! Declarations of `Proofs18FejerCubicParameters` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open scoped BigOperators

/-- Convert the common-cell-length count to a power of the old modulus. -/
theorem fejer_cubic_twisted_count_power {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1)
    {N l J : Nat} [NeZero N]
    (hl : (N : Real) ^ fejerCubicLocalizationExponent alpha / 12 ≤ l)
    (hcount : (J : Real) ≤ fejerCubicLocalCountConstant alpha * N / (l : Real) ^ fejerCubicLocalCountExponent alpha) :
    (J : Real) ≤ fejerCubicTwistedCountConstant alpha *
      (N : Real) ^ (1 - fejerCubicLocalizationExponent alpha * fejerCubicLocalCountExponent alpha) := by
  exact partition_count_power_of_length (fejerCubicLocalCountExponent_bounds hα hαone).1.le
    (zero_le_one.trans (le_max_left _ _)) (by norm_num) hl hcount

end

end LeanProofs.GowersSzemeredi
