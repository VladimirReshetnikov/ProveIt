import GowersSzemeredi.Proofs18ExplicitCubicDiscrepancy
import GowersSzemeredi.Proofs18GeneralIteration

/-! A closed five-term Szemerédi threshold from the constructed cubic inverse theorem.
No comparison with the paper's numerical five-term bound is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def fiveTermThreshold (delta : Real) : Real :=
  intervalDiscrepancyClosedThreshold 5 delta
    (cubicDiscrepancyParameter (intervalUniformityParameter delta 5))
    (cubicDiscrepancyExponent (intervalUniformityParameter delta 5))
    (cubicInverseThreshold (intervalUniformityParameter delta 5))

/-- Every sufficiently large interval subset of density delta contains a
five-term arithmetic progression, with a fully specified finite threshold. -/
theorem natural_five_term_explicit (delta : Real)
    (hδ : 0 < delta) (hδone : delta ≤ 1)
    (N : Nat) (hN : fiveTermThreshold delta ≤ (N : Real))
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 N) (hcard : delta * N ≤ A.card) :
    HasNatAP A 5 := by
  have hα := intervalUniformityParameter_pos (k := 5) hδ (by omega)
  have hαone := intervalUniformityParameter_le_one (k := 5) hδ.le hδone (by omega)
  exact (cubic_function_discrepancy_bound_explicit hα hαone).natural_szemeredi_closed
    (by omega) hδ (cubicDiscrepancyParameter_pos hα)
    (cubicDiscrepancyExponent_pos hα hαone) N hN A hA hcard

end LeanProofs.GowersSzemeredi
