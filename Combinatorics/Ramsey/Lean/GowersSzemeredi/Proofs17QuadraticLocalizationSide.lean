import GowersSzemeredi.Proofs17QuadraticLocalization
import GowersSzemeredi.Proofs13IntegerBudgets

/-! Declarations of `Proofs17QuadraticLocalization` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- A quadratic twist lowers the obstruction degree on a partition into
proper progressions, with explicit surviving parameter and length exponent. -/
theorem quadratic_nonuniformity_localized_phase_removal :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 2 →
        ∃ phi : ZMod N → ZMod N, ∃ M l : Nat, ∃ Q : Fin M → ModAP N,
          PolynomialOn 2 Finset.univ phi ∧
          IsPartition (fun i ↦ (Q i).carrier) Finset.univ ∧
          (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
          (N : Real) ^ cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 / 6 ≤ l ∧
          (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
          ¬ UniformOnPartition (phaseTwist f phi) 1
            ((2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat)) Q (l + 1) := by
  intro alpha hα hαone
  have he := (quadratic_frequency_exponent_bounds hα hαone).1
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_nat_mul_rpow_le (C := 4) (D := 1) he zero_lt_one)
  refine ⟨N₀, fun N _ _ hN ↦ ?_⟩
  apply quadratic_nonuniformity_localized_phase_removal_of_power_bound alpha hα hαone N
  simpa only [Real.rpow_zero, mul_one, one_mul] using hN₀ N hN

end LeanProofs.GowersSzemeredi
