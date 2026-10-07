import GowersSzemeredi.Proofs18GeneralPhaseInverseAssembly
import GowersSzemeredi.Proofs18FejerCubicParameters
import GowersSzemeredi.Proofs18CubicDiscrepancy
import GowersSzemeredi.Proofs18FejerCubicTwistedDiscrepancy

/-! A fully explicit threshold for the cubic function inverse theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def fejerCubicInverseThreshold (alpha : Real) : Real :=
  max (fejerCubicTwistedThreshold alpha)
    (positivePowerThreshold (fejerCubicPhaseRefinementConstant alpha) 1
      (fejerCubicDiscrepancyExponent alpha))

/-- Every disc-valued function failing cubic uniformity has an untwisted
proper discrepancy partition, with explicit positive discrepancy and average
size parameters and an explicit modulus threshold. -/
theorem fejer_cubic_nonuniformity_discrepancy_partition (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerCubicInverseThreshold alpha ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ J : Nat, ∃ R : Fin J → ModAP N,
        IsPartition (fun j => (R j).carrier) Finset.univ ∧
        (∀ j, (R j).IsProper) ∧
        (N : Real) ^ fejerCubicDiscrepancyExponent alpha ≤ averageCellSize (fun j => (R j).carrier) ∧
        fejerCubicDiscrepancyParameter alpha * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  let e := fejerCubicLocalizationExponent alpha * fejerCubicLocalCountExponent alpha
  let beta := fejerCubicTwistedDiscrepancyParameter alpha
  let D := fejerCubicTwistedCountConstant alpha
  have he : 0 < e := mul_pos (by unfold fejerCubicLocalizationExponent; positivity)
    (fejerCubicLocalCountExponent_bounds hα hαone).1
  have hβ : 0 < beta := by
    have h := fejerCubicDiscrepancyParameter_pos hα
    change 0 < beta / 2 at h
    linarith only [h]
  have hD : 0 < D := by
    have h := lt_of_lt_of_le zero_lt_one (le_max_left (1 : Real)
      (2 * boundaryRefinementConstant (1 / 16) * (8 : Real) ^ (1 - fejerCubicLocalCountExponent alpha)))
    dsimp [D, fejerCubicTwistedCountConstant, fejerCubicLocalCountConstant]
    positivity
  intro N _ _ hN f hf hnot
  obtain ⟨phi, l, K, Q, hpoly, hlength, hQ, _, hcount, hdis⟩ :=
    fejer_cubic_nonuniformity_twisted_discrepancy alpha hα hαone N
      ((le_max_left _ _).trans hN) f hf hnot
  have hcount' : (K : Real) ≤ D * (N : Real) ^ (1 - e) :=
    fejer_cubic_twisted_count_power hα hαone hlength hcount
  exact polynomial_phase_inverse_partition (by omega : 1 ≤ 3) he hβ hD f hf
    Q (fun _ => phi) (fun _ => hpoly) hQ hcount' hdis ((le_max_right _ _).trans hN)

/-- The cubic inverse interface with every threshold specified by a finite formula. -/
theorem fejer_cubic_function_discrepancy_bound {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    FunctionDiscrepancyBound 3 alpha (fejerCubicDiscrepancyParameter alpha)
      (fejerCubicDiscrepancyExponent alpha) (fejerCubicInverseThreshold alpha) := by
  intro N _ _ hN f hf hnot
  exact fejer_cubic_nonuniformity_discrepancy_partition alpha hα hαone N hN f hf hnot

end LeanProofs.GowersSzemeredi
