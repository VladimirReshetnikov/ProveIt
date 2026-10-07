import GowersSzemeredi.Proofs18FejerCubicDiscrepancy
import GowersSzemeredi.Proofs18GeneralIteration

/-! A closed five-term Szemerédi threshold from the constructed cubic inverse theorem.
No comparison with the paper's numerical five-term bound is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def fejerFiveTermThreshold (delta : Real) : Real :=
  intervalDiscrepancyClosedThreshold 5 delta
    (fejerCubicDiscrepancyParameter (intervalUniformityParameter delta 5))
    (fejerCubicDiscrepancyExponent (intervalUniformityParameter delta 5))
    (fejerCubicInverseThreshold (intervalUniformityParameter delta 5))

/-- Every sufficiently large interval subset of density delta contains a
five-term arithmetic progression, with a fully specified finite threshold. -/
theorem natural_five_term_fejer (delta : Real)
    (hδ : 0 < delta) (hδone : delta ≤ 1)
    (N : Nat) (hN : fejerFiveTermThreshold delta ≤ (N : Real))
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 N) (hcard : delta * N ≤ A.card) :
    HasNatAP A 5 := by
  have hα := intervalUniformityParameter_pos (k := 5) hδ (by omega)
  have hαone := intervalUniformityParameter_le_one (k := 5) hδ.le hδone (by omega)
  exact (fejer_cubic_function_discrepancy_bound hα hαone).natural_szemeredi_closed
    (by omega) hδ (fejerCubicDiscrepancyParameter_pos hα)
    (fejerCubicDiscrepancyExponent_pos hα hαone) N hN A hA hcard

end LeanProofs.GowersSzemeredi
