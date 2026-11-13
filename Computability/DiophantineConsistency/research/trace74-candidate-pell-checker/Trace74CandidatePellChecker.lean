import Trace74PowerPeriodResidue
import Trace74PellBitlistChecker

/-! Candidate coefficient and bit-list evaluator composition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CandidatePellChecker
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticPellRecurrence
open Trace74PellCoefficientReduction Trace74PowerPeriodResidue Trace74PellBitlistChecker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def candidateBits : List Bool :=
  [true, false, true, true, false, true, true, false,
   false, false, true, true, false, false, false, false,
   true, true, false, false, true, true, false, false,
   false, true, false, true, false, false, false, true]

/-- Under the symbolic candidate's q/modulus/base bindings, the checker
uses the sparse coefficient residues, with no huge power evaluated. -/
theorem candidate_run (b q m : V) (bits : List Bool) (hm : 0<m)
    (hq : q=power 2 590069) (hqm : q*q=m+1)
    (hb : b+1=(q*q*q)*(power 2 3056651345+1)) :
    let x := power 2 93925
    let L := q*(x+1)+1
    let D := (x+1)*(x+1)+2*q*(x+1)
    xcoord (runIndex bits) b%m=(run m L D bits).1 ∧
      ycoord (runIndex bits) b%m=(run m L D bits).2 := by
  have hx := candidate_power_period q m hm hq hqm
  obtain ⟨hL,hD⟩ := sparse_coefficients q m (power 2 3056651345)
    (power 2 93925) hm hqm hx
  apply run_correct b m _ _ bits hm
  · rw [show b+2=(b+1)+1 by ring,hb]
    exact hL
  · unfold delta
    rw [show b+3=(b+1)+2 by ring,hb]
    exact hD

/-- The bit list encodes the exact candidate Pell index in every model. -/
theorem candidate_index : (runIndex candidateBits : V)=3056651345 := by
  norm_num [candidateBits,runIndex,stepIndex]

/-- Candidate-index specialization of the sparse modular evaluator. -/
theorem candidate_run_at_index (b q m : V) (hm : 0<m)
    (hq : q=power 2 590069) (hqm : q*q=m+1)
    (hb : b+1=(q*q*q)*(power 2 3056651345+1)) :
    let x := power 2 93925
    let L := q*(x+1)+1
    let D := (x+1)*(x+1)+2*q*(x+1)
    xcoord 3056651345 b%m=(run m L D candidateBits).1 ∧
      ycoord 3056651345 b%m=(run m L D candidateBits).2 := by
  simpa only [candidate_index] using candidate_run b q m candidateBits hm hq hqm hb

#print axioms Trace74CandidatePellChecker.candidate_run
#print axioms Trace74CandidatePellChecker.candidate_index
#print axioms Trace74CandidatePellChecker.candidate_run_at_index
end Trace74CandidatePellChecker
