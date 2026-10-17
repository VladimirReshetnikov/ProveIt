import GowersSzemeredi.Proofs13FejerExplicitExponent
import GowersSzemeredi.Proofs13FejerFourierExtractionSide

/-! Declarations of `Proofs13FejerExplicitExponent` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem theorem_13_12_fejer_explicit_threshold :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], section13FourierThreshold alpha ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  intro N _ _ hN f hf hnot
  obtain ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, hsize, hbox, hmass, hbil, hfourier⟩ :=
    theorem_13_12_fejer_extraction_explicit alpha hα hαone N hN f hf hnot
  refine ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, ?_, hbox, hmass, hbil, hfourier⟩
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  exact (Real.rpow_le_rpow_of_exponent_le hNreal (section13_fejer_exponent_lower hα hαone)).trans hsize

theorem theorem_13_12_with_fejer_explicit_bound :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  refine ⟨Nat.ceil (section13FourierThreshold alpha), fun N _ _ hN => ?_⟩
  exact theorem_13_12_fejer_explicit_threshold alpha hα hαone N
    ((Nat.le_ceil _).trans (by exact_mod_cast hN))

end LeanProofs.GowersSzemeredi
