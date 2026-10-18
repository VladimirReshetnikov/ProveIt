import GowersSzemeredi.Proofs13FejerPurifiedDensity

/-! Declarations of `Proofs13FejerPurifiedDensity` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_density_uniform
    (delta rho eta : Real) (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ N₀ : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
      ∀ (U : Finset (Pair N)) (phi : Pair N → ZMod N) (beta : Real), delta ≤ beta →
      (U.card : Real) = beta * (N : Real) ^ 2 →
      rho * beta ^ 15 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 U phi →
      ∃ S ⊆ U,
        ((2 : Real) ^ 77)⁻¹ * rho ^ 3 * eta ^ 3 * beta * (N : Real) ^ 2 ≤ (S.card : Real) ∧
        (1 - eta) * (arrangementCount 8 S : Real) ≤ (respectedArrangementCount 8 S phi : Real) := by
  exact ⟨fejerPurificationThreshold delta rho eta,
    section13_fejer_density_explicit delta rho eta hdelta hrho hrho1 heta heta1⟩

end LeanProofs.GowersSzemeredi
