import GowersSzemeredi.Proofs18CubicCellModels
import GowersSzemeredi.Proofs18SupportedFunctionDiscrepancy

/-! Actual quadratic discrepancy on a positive mass of cubic localization
cells, with the interval boundary loss and local cell count controlled. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- On a positive mass of the original partition, cubic nonuniformity
produces interior discrepancy families in comparable smaller prime models.
Both the count exponent and surviving discrepancy are uniform across cells.
This is an unconditional local statement; assembling and untwisting a global
cubic discrepancy partition still requires further geometry. -/
theorem cubic_nonuniformity_local_discrepancy (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) : ∃ N₀ : Nat,
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) / 12 ≤ l ∧
        ∃ B : Finset (Fin K),
          cubicLocalizedMassParameter alpha * N < ∑ i ∈ B, ((Q i).carrier.card : Real) ∧
          ∀ i ∈ B, ∃ M : Nat, ∃ hM : M.Prime,
            letI : NeZero M := ⟨hM.ne_zero⟩
            4 * (Q i).length < M ∧ M ≤ 8 * (Q i).length ∧ (M : Real) ≤ (N : Real) / 2 ∧
            ∃ J : Nat, ∃ R : Fin J → ModAP M,
              IsPartition (fun j => (R j).carrier) Finset.univ ∧
              (∀ j, (R j).IsProper) ∧
              (J : Real) ≤ boundaryRefinementConstant
                (quadraticDiscrepancyParameter (cubicLocalQuadraticParameter alpha) / 64) *
                (M : Real) ^ (1 - quadraticDiscrepancyExponent (cubicLocalQuadraticParameter alpha) / 16) ∧
              ∃ G : Finset (Fin J),
                (∀ j ∈ G, (R j).carrier ⊆ finiteIntervalImage M (Finset.univ : Finset (Fin (Q i).length))) ∧
                (7 * quadraticDiscrepancyParameter (cubicLocalQuadraticParameter alpha) / 8) * M ≤
                  ∑ j ∈ G, ‖∑ x ∈ (R j).carrier,
                    intervalExtension M ((Q i).pullbackFunction (phaseTwist f phi)) x‖ := by
  let a := cubicLocalQuadraticParameter alpha
  let b := quadraticDiscrepancyParameter a
  have ha : 0 < a := cubicLocalQuadraticParameter_pos hα
  have haone : a ≤ 1 := cubicLocalQuadraticParameter_le_one hα.le hαone
  have hb : 0 < b := by dsimp [b, quadraticDiscrepancyParameter]; positivity
  let T := max (quadraticExponentialThreshold a) (32 / b)
  obtain ⟨N₀, hN₀⟩ := cubic_nonuniformity_many_prime_models alpha T hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨phi, K, l, Q, hpoly, hQ, hproper, hlength, B, hmass, hB⟩ := hN₀ N hN f hf hnot
  refine ⟨phi, K, l, Q, hpoly, hQ, hproper, hlength, B, hmass, ?_⟩
  intro i hi
  obtain ⟨M, hM, hT, hMlow, hMup, hMhalf, hdisc, hnon⟩ := hB i hi
  letI : NeZero M := ⟨hM.ne_zero⟩
  letI : Fact M.Prime := ⟨hM⟩
  have hthreshold : quadraticExponentialThreshold a ≤ (M : Real) :=
    (le_max_left _ _).trans hT
  have hscale : 32 ≤ b * M := by
    have h := (div_le_iff₀ hb).mp ((le_max_right _ _).trans hT)
    simpa only [mul_comm] using h
  obtain ⟨J, R, hR, hRproper, hcount, G, hG, hdis⟩ :=
    (quadratic_function_discrepancy_bound ha haone).interval_supported_discrepancy
      hb (by omega) hthreshold hscale ((Q i).pullbackFunction (phaseTwist f phi)) hdisc hnon
  exact ⟨M, hM, hMlow, hMup, hMhalf, J, R, hR, hRproper, hcount, G, hG, hdis⟩

end LeanProofs.GowersSzemeredi
