module
public import M6PA.Scheduler.SourceEnumerationSuffixInduction
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open M6.PA.SourceCommandEncodingInternal
open M6.PA.ActualCandidateBlueprint M6.PA.ActualWordEncodingBlueprint
open M6.PA.SourceCantorInternal M6.PA.ActualCommandStepGraph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem refutation_from_two (code initial : V)
    (hc : M6.PA.ActualCheckerBlueprint.verifyValue code=2) :
    fromValue 2 (candidateValue code-2+1) initial=0 := by
  rw [from_succ,add_tsub_self_of_le (candidate_ge_two code)]
  exact refutation_candidate_run code _ hc

/-- The exact source starts at candidate2, not candidate0. No arithmetic word
is lost: the universal reset/compiled/shift candidate has code at least2. -/
theorem refutation_root_two_halts (code xs : V) (hv : ValidStore xs) (hc : CommandClean xs)
    (hn : registers xs 0=2) (hl : registers xs 8=0)
    (hcode : M6.PA.ActualCheckerBlueprint.verifyValue code=2) :
    ∃ k cs d, Trace k cs (stateCode 1 xs) d ∧ control d=0 := by
  have hr := commandRelation_root xs hv hc
  rw [hn,hl] at hr
  obtain ⟨k,cs,d,ht,hd⟩ := source_from (candidateValue code-2+1) 2
    (stateCode 1 xs) (commandState xs) hr
  rw [refutation_from_two code _ hcode] at hd
  exact ⟨k,cs,d,ht,commandRelation_zero _ _ _ hd⟩
#print axioms candidate_ge_two
#print axioms source_from
#print axioms refutation_root_two_halts
end M6.Arithmetic.PA.InternalTrace.CodedSource
