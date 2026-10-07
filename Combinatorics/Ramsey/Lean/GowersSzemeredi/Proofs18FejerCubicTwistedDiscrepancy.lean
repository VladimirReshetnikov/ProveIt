import GowersSzemeredi.Proofs18GeneralLocalInverseAssembly
import GowersSzemeredi.Proofs18FejerCubicParameters
import GowersSzemeredi.Proofs18CubicTwistedDiscrepancy
import GowersSzemeredi.Proofs18FejerCubicCellModels

/-! Explicit modulus threshold for the global cubic twisted discrepancy partition. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def fejerCubicTwistedThreshold (alpha : Real) : Real :=
  fejerCubicPrimeModelThreshold alpha
    (max 4 (quadraticExponentialThreshold (fejerCubicLocalQuadraticParameter alpha)))

/-- Cubic nonuniformity yields a full proper discrepancy partition for one
cubic twist. The explicit count is scaled by the common original cell
length, which retains the Section 13 positive-power lower bound. -/
theorem fejer_cubic_nonuniformity_twisted_discrepancy (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerCubicTwistedThreshold alpha ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ l J : Nat, ∃ R : Fin J → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        (N : Real) ^ fejerCubicLocalizationExponent alpha / 12 ≤ l ∧
        IsPartition (fun j => (R j).carrier) Finset.univ ∧
        (∀ j, (R j).IsProper) ∧
        (J : Real) ≤ fejerCubicLocalCountConstant alpha * N / (l : Real) ^ fejerCubicLocalCountExponent alpha ∧
        fejerCubicTwistedDiscrepancyParameter alpha * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, phaseTwist f phi x‖ := by
  let a := fejerCubicLocalQuadraticParameter alpha
  let b := quadraticDiscrepancyParameter a
  have ha : 0 < a := fejerCubicLocalQuadraticParameter_pos hα
  have haone : a ≤ 1 := fejerCubicLocalQuadraticParameter_le_one hα.le hαone
  have hb : 0 < b := by dsimp [b, quadraticDiscrepancyParameter]; positivity
  obtain ⟨ht, htone⟩ := fejerCubicLocalCountExponent_bounds hα hαone
  intro N _ _ hN f hf hnot
  obtain ⟨phi, K, l, Q, hpoly, hQ, hproper, hlength, B, hmass, hB⟩ :=
    fejer_cubic_nonuniformity_many_prime_models alpha
      (max 4 (quadraticExponentialThreshold a)) hα hαone N hN f hf hnot
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hlpos : (0 : Real) < l :=
    (by positivity : 0 < (N : Real) ^ fejerCubicLocalizationExponent alpha / 12).trans_le hlength
  have hl : 1 ≤ l := by exact_mod_cast (show (1 : Real) ≤ l from by
    have hh : 0 < l := by exact_mod_cast hlpos
    exact_mod_cast hh)
  have hσ : 0 ≤ quadraticDiscrepancyExponent a := by
    change 0 < quadraticDiscrepancyExponent a / 16 at ht
    linarith only [ht]
  have hσ16 : quadraticDiscrepancyExponent a ≤ 16 := by
    change quadraticDiscrepancyExponent a / 16 ≤ 1 at htone
    linarith only [htone]
  have hmodels (i : Fin K) (hi : i ∈ B) : ∃ M : Nat, ∃ hM : M.Prime,
      letI : NeZero M := ⟨hM.ne_zero⟩
      4 ≤ M ∧ (Q i).length ≤ M ∧ quadraticExponentialThreshold a ≤ (M : Real) ∧
      (M : Real) ≤ 8 * (Q i).length ∧
      ¬ UniformOfDegree (intervalExtension M ((Q i).pullbackFunction (phaseTwist f phi))) a 2 := by
    obtain ⟨M, hM, hT, hMlow, hMup, _, _, hnon⟩ := hB i hi
    letI : NeZero M := ⟨hM.ne_zero⟩
    refine ⟨M, hM, ?_, by omega, (le_max_right _ _).trans hT, ?_, hnon⟩
    · exact_mod_cast ((le_max_left _ _).trans hT : (4 : Real) ≤ M)
    · exact_mod_cast hMup
  obtain ⟨J, R, hR, hp, hc, hd⟩ :=
    (quadratic_function_discrepancy_bound ha haone).selected_prime_model_partition
      hb.le hσ hσ16 (by norm_num : (0 : Real) ≤ 8)
      (phaseTwist f phi) (phaseTwist_discValued hf phi) Q B hQ (fun i => (hproper i).1) hl
      (fun i => by rcases (hproper i).2 with hi | hi <;> omega) hmodels
  refine ⟨phi, l, J, R, hpoly, hlength, hR, hp, hc, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hmass.le hb.le
  have hm' : fejerCubicTwistedDiscrepancyParameter alpha * N ≤
      b * ∑ i ∈ B, ((Q i).carrier.card : Real) := by
    change (fejerCubicLocalizedMassParameter alpha * b) * N ≤ _
    nlinarith only [hm]
  exact hm'.trans hd

end LeanProofs.GowersSzemeredi
