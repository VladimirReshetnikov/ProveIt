module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCommandRelation
public import PA196.Arithmetic.Scheduler.InternalCodedSourceDispatchCommands
@[expose] public section
open PA196.Arithmetic.Machine.PA
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]

theorem commandRelation_of_outcome (c n l s : V)
    (hp : control c=0 ∨ control c=26) (hv : ValidStore (store c)) (hc : CommandClean (store c))
    (hn : registers (store c) 0=n) (hl : registers (store c) 8=l) (hs : commandObservation c=s) :
    CommandRelation c n l s := by
  rcases hp with hp|hp
  · left
    have hz : s=0 := by simpa [commandObservation,hp] using hs.symm
    exact ⟨hz,hp⟩
  · right
    have hz : commandState (store c)=s := by simpa [commandObservation,hp] using hs
    exact ⟨hp,hv,hc,hn,hl,hz⟩

theorem shiftOutcome_relation (xs : V) (hv : ValidStore xs) (hc : CommandClean xs) :
    CommandRelation (shiftOutcome xs) (registers xs 0) (registers xs 8)
      (CommandStep.stepValue 0 (commandState xs)) := by
  exact commandRelation_of_outcome _ _ _ _ (shiftOutcome_control xs) (shiftOutcome_valid xs hv)
    (shiftOutcome_clean xs hv hc) (shiftOutcome_frame xs hv).1 (shiftOutcome_frame xs hv).2 (shiftOutcome_command xs hv)

theorem dispatchMPEnd_relation (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    CommandRelation (stateCode 26 (dispatchMPEnd xs)) (registers xs 0) (decodeRight (registers xs 8))
      (CommandStep.stepValue (CommandStep.mpCode (decodeLeft (registers xs 8))) (commandState xs)) := by
  have hv' : ValidStore (dispatchMPEnd xs) := mpEnd_valid _ (dispatchMPStore_valid xs hv)
  have hc' : CommandClean (dispatchMPEnd xs) := mpEnd_clean _ (dispatchMPStore_valid xs hv) (dispatchMPStore_clean xs hv hx hy)
  have h := commandRelation_root (dispatchMPEnd xs) hv' hc'
  rw [(dispatchMPEnd_frame xs hv).1,(dispatchMPEnd_frame xs hv).2,dispatchMPEnd_command xs hv] at h
  exact h
#print axioms commandRelation_of_outcome
#print axioms shiftOutcome_relation
#print axioms dispatchMPEnd_relation
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

