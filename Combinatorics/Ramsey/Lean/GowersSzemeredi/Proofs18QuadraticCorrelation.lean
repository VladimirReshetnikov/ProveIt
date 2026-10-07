import GowersSzemeredi.Proofs18QuadraticPrimeModel
import GowersSzemeredi.Proofs18LinearFourierObstruction

/-! Explicit phase correlation of a long interval of the original function.
The quadratic phase lives in the original modulus, while the final linear
character lives in the constructed smaller prime model. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Quadratic nonuniformity gives a quadratic twist of a long progression
with a large linear-character correlation in its actual interval coordinates.
The two character moduli are retained explicitly. -/
theorem quadratic_nonuniformity_interval_correlation :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 2 →
        ∃ phi : ZMod N → ZMod N, ∃ P : ModAP N,
          PolynomialOn 2 Finset.univ phi ∧ P.IsProper ∧
          (N : Real) ^ cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 / 6 ≤ P.length ∧
          ∃ M : Nat, ∃ hM : M.Prime,
            letI : NeZero M := ⟨hM.ne_zero⟩
            3 * P.length < M ∧ M ≤ 6 * P.length ∧ (M : Real) ≤ (N : Real) / 2 ∧
            ∃ r : ZMod M,
              Real.sqrt ((2 : Real) ^ (-(19 : Int)) * alpha ^ 2 *
                  (alpha / 2) ^ (12359 : Nat) / 216) * P.length <
                ‖∑ i : Fin P.length, P.pullbackFunction (phaseTwist f phi) i *
                  exponential (-(r * ((i : Nat) : ZMod M)))‖ := by
  intro alpha hα hαone
  obtain ⟨N₀, hN₀⟩ := quadratic_nonuniformity_prime_model alpha hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot ↦ ?_⟩
  obtain ⟨phi, P, hpoly, hP, hlength, M, hM, hMlow, hMup, hMhalf, hdisc, hfail⟩ :=
    hN₀ N hN f hf hnot
  letI : NeZero M := ⟨hM.ne_zero⟩
  refine ⟨phi, P, hpoly, hP, hlength, M, hM, hMlow, hMup, hMhalf, ?_⟩
  exact interval_linear_nonuniformity_correlation (by omega) _ _ (by positivity) hdisc hfail

end LeanProofs.GowersSzemeredi
