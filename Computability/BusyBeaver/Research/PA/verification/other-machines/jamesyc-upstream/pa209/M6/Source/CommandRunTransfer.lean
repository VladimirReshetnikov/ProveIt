module
public import M6.Source.CommandRunTransferCore
public import M6.Source.CommandTransfer
public import M6.Source.SchedulerInvariant
@[expose] public section
namespace M6.Source.CommandRunTransfer
open Enumeration

/-- The proved actual source macros instantiate the finite-prefix halting
transfer; no conditional macro supplier remains in this theorem. -/
theorem actual_prefix_halts (n : Nat) (p rest : List Command) (hp : word n = p++rest)
    (hbad : commandsEval (schedule n++p) commandInitial = none) :
    CycleHalts exactSites (commandConfig 0 0 0 0 commandInitial) :=
  prefix_halts parsed_command_step n p rest hp hbad

theorem arithmeticSafe_iff_source_nonhalting :
    Scheduler.ArithmeticSafe ↔ ¬ CycleHalts exactSites (commandConfig 0 0 0 0 commandInitial) :=
  ⟨Scheduler.source_scheduler_nonhalting,nonhalting_implies_arithmeticSafe parsed_command_step⟩

#print axioms actual_prefix_halts
#print axioms arithmeticSafe_iff_source_nonhalting
end M6.Source.CommandRunTransfer

