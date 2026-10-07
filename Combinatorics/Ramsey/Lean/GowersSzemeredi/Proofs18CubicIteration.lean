import GowersSzemeredi.Proofs18CubicDiscrepancy
import GowersSzemeredi.Proofs18GeneralIteration

/-! The constructed cubic inverse theorem discharges the five-term density
iteration input. Its remaining existential modulus threshold is kept visible. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The cubic function inverse interface is unconditional, with explicit
parameters and a threshold depending only on alpha. -/
theorem cubic_function_discrepancy_bound {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∃ T : Real, FunctionDiscrepancyBound 3 alpha (cubicDiscrepancyParameter alpha)
      (cubicDiscrepancyExponent alpha) T := by
  obtain ⟨N₀, hN₀⟩ := cubic_nonuniformity_discrepancy_partition alpha hα hαone
  refine ⟨N₀, ?_⟩
  intro N _ _ hN f hf hnot
  exact hN₀ N (by exact_mod_cast hN) f hf hnot

/-- End-to-end five-term Szemeredi iteration through the proved cubic
inverse theorem. The closed iteration threshold retains the still-existential
inverse threshold T, so this does not assert the source's numerical bound. -/
theorem natural_five_term_via_cubic_inverse (delta : Real)
    (hδ : 0 < delta) (hδone : delta ≤ 1) : ∃ T : Real,
    ∀ N : Nat,
      intervalDiscrepancyClosedThreshold 5 delta
        (cubicDiscrepancyParameter (intervalUniformityParameter delta 5))
        (cubicDiscrepancyExponent (intervalUniformityParameter delta 5)) T ≤ N →
      ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → delta * N ≤ A.card → HasNatAP A 5 := by
  have hα := intervalUniformityParameter_pos (k := 5) hδ (by omega)
  have hαone := intervalUniformityParameter_le_one (k := 5) hδ.le hδone (by omega)
  obtain ⟨T, hT⟩ := cubic_function_discrepancy_bound hα hαone
  refine ⟨T, fun N hN A hA hcard => ?_⟩
  exact hT.natural_szemeredi_closed (by omega) hδ (cubicDiscrepancyParameter_pos hα)
    (cubicDiscrepancyExponent_pos hα hαone) N hN A hA hcard

end LeanProofs.GowersSzemeredi
