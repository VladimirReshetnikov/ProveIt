import GowersSzemeredi.Proofs18RefinementThresholdBounds

/-! Declarations of `Proofs18RefinementThresholdBounds` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The phase-refinement estimate with the original polynomial partition budget. -/
theorem inv_thr_le_ex {X : Real} (hX : 2 ≤ X) {k : Nat} {η β e σ : Real} {M s : Nat}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hηi : η⁻¹ ≤ X ^ (2 ^ M)) (hβi : β⁻¹ ≤ X ^ (2 ^ M)) (hs0 : 0 < σ) (hs16 : σ ≤ 16)
    (hσ'0 : 0 < inverseStepExponent (k + 1) e σ)
    (hσ' : (inverseStepExponent (k + 1) e σ)⁻¹ ≤ Real.exp (X ^ (2 ^ s))) :
    inverseStepThreshold (k + 1) η β e (6 * ((k + 1 : Nat) : Real)) σ ≤
      Real.exp (Real.exp (X ^ (2 ^ (max (max (M + 4 * (k + 3) ^ 2 + 4) (k + 16)) s + 1)))) := by
  exact inv_thr_le_ex_of_partition_bound hX
    (by simpa only [show k + 1 + 1 + 1 = k + 3 by omega] using polyPartConst_le (k + 1 + 1))
    hη0 hη1 hβ0 hβ1 hηi hβi hs0 hs16 hσ'0 hσ'

end LeanProofs.GowersSzemeredi
