import GowersSzemeredi.Proofs13ImprovedPrintedEndpoint

/-! Strengthen Theorem 13.12 simultaneously: the top length exponent
is 2^61 instead of 2^70, and the density exponent is 2^42 instead of
2^76, uniformly for all 0<alpha<=1. This is an auxiliary improvement,
not yet a strengthened final quantitative Szemeredi theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem theorem_13_12_with_improved_printed_bounds :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 61))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  by_cases haway : alpha ≤ 332 / 333
  · obtain ⟨N₀, hN₀⟩ := theorem_13_12_with_fejer_explicit_bound alpha hα hαone
    refine ⟨N₀, fun N _ _ hN f hf hnot => ?_⟩
    obtain ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, hsize, hbox, hmass, hbil, hfourier⟩ :=
      hN₀ N hN f hf hnot
    refine ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, ?_, hbox, hmass, hbil, hfourier⟩
    have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
    exact (Real.rpow_le_rpow_of_exponent_le hNreal
      (section13_improved_printed_exponent_comparison hα haway)).trans hsize
  · exact theorem_13_12_improved_near_one alpha (lt_of_not_ge haway) hαone

end LeanProofs.GowersSzemeredi
