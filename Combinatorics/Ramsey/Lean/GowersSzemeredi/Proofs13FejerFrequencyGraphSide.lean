import GowersSzemeredi.Proofs13FejerFrequencyGraph

/-! Declarations of `Proofs13FejerFrequencyGraph` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_frequency_graph (alpha : Real) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∃ N₀ : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ A : Finset (Pair N), ∃ phi : Pair N → ZMod N,
        (alpha / 2) ^ (4207554485 : Nat) * (N : Real) ^ 2 ≤ A.card ∧
        SeparatelyFreimanEight A phi ∧ MostlyRespectsEight A phi ((2 : Real) ^ (-(44 : Int))) ∧
        ∀ z, z ∈ A → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  exact ⟨section13FrequencyGraphThreshold alpha,
    section13_fejer_frequency_graph_explicit alpha halpha halpha1⟩

end LeanProofs.GowersSzemeredi
