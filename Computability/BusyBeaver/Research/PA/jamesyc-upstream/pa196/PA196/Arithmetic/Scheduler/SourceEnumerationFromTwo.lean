module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.SourceEnumerationSuffixInduction
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal
open PA196.Arithmetic.Scheduler.ActualCandidateBlueprint PA196.Arithmetic.Scheduler.ActualWordEncodingBlueprint
open M6.PA.SourceCantorInternal PA196.Arithmetic.CommandStep

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
theorem refutation_from_two (code initial : V)
    (hc : PA196.Arithmetic.Checker.verifyValue code=2) :
    fromValue 2 (candidateValue code-2+1) initial=0 := by
  rw [from_succ,add_tsub_self_of_le (candidate_ge_two code)]
  exact refutation_candidate_run code _ hc

/-- The exact source starts at candidate2, not candidate0. No arithmetic word
is lost: the universal reset/compiled/shift candidate has code at least2. -/
theorem refutation_root_two_halts (code xs : V) (hv : ValidStore xs) (hc : CommandClean xs)
    (hn : registers xs 0=2) (hl : registers xs 8=0)
    (hcode : PA196.Arithmetic.Checker.verifyValue code=2) :
    ∃ k cs d, Trace k cs (stateCode 26 xs) d ∧ control d=0 := by
  have hr := commandRelation_root xs hv hc
  rw [hn,hl] at hr
  obtain ⟨k,cs,d,ht,hd⟩ := source_from (candidateValue code-2+1) 2
    (stateCode 26 xs) (commandState xs) hr
  rw [refutation_from_two code _ hcode] at hd
  exact ⟨k,cs,d,ht,commandRelation_zero _ _ _ hd⟩
#print axioms candidate_ge_two
#print axioms source_from
#print axioms refutation_root_two_halts
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
