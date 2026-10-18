import GowersSzemeredi.Proofs16ShortScale

/-! Declarations of `Proofs16ShortScale` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The Section 16 radius is at most one half, uniformly over its stated
parameter range. -/
theorem section16Zeta_pos_le_half {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16Zeta theta gamma k ∧ section16Zeta theta gamma k ≤ 1 / 2 := by
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hp1 : theta * gamma ≤ 1 := by nlinarith
  have hb : (1 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ hp).mpr (by linarith)
  have hS : 1 ≤ multipleS theta gamma k := one_le_pow₀ hb
  constructor
  · unfold section16Zeta; positivity
  · unfold section16Zeta
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) (neg_le_neg hS)
    norm_num at h
    exact h

end LeanProofs.GowersSzemeredi
