import GowersSzemeredi.Proofs13FejerUniformPurification

/-! Declarations of `Proofs13FejerUniformPurification` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_purification_uniform
    (delta rho eta : Real) (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ N₀ : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
      ∀ (U : Finset (Pair N)) (phi : Pair N → ZMod N) (beta : Real), delta ≤ beta →
      (U.card : Real) = beta * (N : Real) ^ 2 →
      rho * beta ^ 15 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 U phi →
      ∃ S ⊆ U,
        ((2 : Real) ^ 1150)⁻¹ * rho ^ 32 * eta ^ 31 * beta ^ 15 * (N : Real) ^ 32 ≤
          (respectedArrangementCount 8 S phi : Real) ∧
        (arrangementCount 8 S : Real) ≤ (1 + eta) * (respectedArrangementCount 8 S phi : Real) := by
  exact ⟨fejerPurificationThreshold delta rho eta,
    section13_fejer_purification_explicit delta rho eta hdelta hrho hrho1 heta heta1⟩

end LeanProofs.GowersSzemeredi
