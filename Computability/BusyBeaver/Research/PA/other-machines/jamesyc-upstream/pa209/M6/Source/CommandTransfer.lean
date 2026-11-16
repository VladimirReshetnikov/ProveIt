module
public import M6.Source.CommandAX
public import M6.Source.ParsedCommandTransfer
@[expose] public section
namespace M6.Source
open Enumeration
/-- All three actual macros instantiate the proved parser/source composition. -/
theorem parsed_command_step (n l : Nat) (s out : CommandStore)
    (he : commandEval (parse (FetchDispatch.seed n l)).command s = some out) :
    ∃ m, 0 < m ∧ CycleSteps exactSites m (commandConfig 0 n l 0 s)
      (commandConfig 0 (FetchDispatch.nextN n l) (parse (FetchDispatch.seed n l)).next 0 out) :=
  parsed_command_step_of_ax ax_command n l s out he
#print axioms parsed_command_step
end M6.Source

