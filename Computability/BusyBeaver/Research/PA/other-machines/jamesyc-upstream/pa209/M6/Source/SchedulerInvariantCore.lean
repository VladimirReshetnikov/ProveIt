module
public import M6.Source.ParsedCommandTransfer
public import M6.Source.SchedulerSafety
@[expose] public section
namespace M6.Source.Scheduler
open Enumeration

/-- Source boundary configurations carry their exact arithmetic history and
N/L frontier. No bound on the number of commands or field values is imposed. -/
def ScheduledState (c : Configuration) : Prop :=
  ∃ n l s history, c = commandConfig 0 n l 0 s ∧ Frontier n l history ∧
    commandsEval history commandInitial = some s

variable (hstep : ∀ (n l : Nat) (s out : CommandStore),
  commandEval (parse (FetchDispatch.seed n l)).command s = some out →
  ∃ m, 0 < m ∧ CycleSteps exactSites m (commandConfig 0 n l 0 s)
    (commandConfig 0 (FetchDispatch.nextN n l) (parse (FetchDispatch.seed n l)).next 0 out))
include hstep

theorem scheduled_progress (h : ArithmeticSafe) (c : Configuration) (hc : ScheduledState c) :
    ∃ m d, 0 < m ∧ CycleSteps exactSites m c d ∧ ScheduledState d := by
  obtain ⟨n,l,s,history,rfl,hfront,he⟩ := hc
  obtain ⟨out,hout,hhistory⟩ := next_result h hfront he
  obtain ⟨m,hm,hsteps⟩ := hstep n l s out hout
  refine ⟨m,_,hm,hsteps,FetchDispatch.nextN n l,(parse (FetchDispatch.seed n l)).next,
    out,history++[(parse (FetchDispatch.seed n l)).command],rfl,advance hfront,hhistory⟩

/-- Generic source scheduler invariant, supplied with a literal macro-step
transfer theorem and the explicitly bridged arithmetic
schedule theorem. Every source macro and every parsing field is accounted for. -/
theorem scheduler_nonhalting_of_transfer (h : ArithmeticSafe) :
    ¬ CycleHalts exactSites (commandConfig 0 0 0 0 commandInitial) := by
  apply cycle_not_halts_of_positive_invariant exactSites ScheduledState
  · intro c hc
    obtain ⟨n,l,s,history,rfl,_,_⟩ := hc
    simp [commandConfig]
  · exact scheduled_progress hstep h
  · exact ⟨0,0,commandInitial,[],rfl,initial,rfl⟩
#print axioms scheduler_nonhalting_of_transfer
end M6.Source.Scheduler

