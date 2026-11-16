module
public import M6.Source.CommandSMP
@[expose] public section
namespace M6.Source
open Cantor Enumeration

theorem command_none_shift (c : Command) (s : CommandStore)
    (he : commandEval c s = none) : c = .shift ∧ s.t+s.h = 1 := by
  cases c with
  | shift =>
    by_cases hh : s.t+s.h = 1
    · exact ⟨rfl,hh⟩
    · simp [commandEval,hh] at he
  | mp x =>
    by_cases hh : AXCode.wim s.t (s.d+x) = s.h <;> simp [commandEval,hh] at he
  | ax c x y => simp [commandEval] at he

theorem shift_command_halts (n l : Nat) (s : CommandStore) (hh : s.t+s.h = 1) :
    CycleHalts exactSites (commandConfig 3911 n l 0 s) := by
  rcases s with ⟨t,w,d,h⟩
  have hs := S36Command.cyclic_halt_of_sum_one t w h (commandRegisters n l 0 ⟨0,0,d,0⟩) hh
  refine ⟨6*t+7*h+10,?_⟩
  have he := congrArg Configuration.control hs.eq_run
  simpa only [S36Command.start,S36Command.halted,command_s_registers,commandConfig] using he

/-- An arithmetic `none` is the actual S guard halt after the exact fetch and
field parse; it is not a synthetic failure state introduced by the interpreter. -/
theorem parsed_command_halts (n l : Nat) (s : CommandStore)
    (he : commandEval (parse (FetchDispatch.seed n l)).command s = none) :
    CycleHalts exactSites (commandConfig 0 n l 0 s) := by
  obtain ⟨hcmd,hh⟩ := command_none_shift _ s he
  have hk : (decode (FetchDispatch.seed n l)).1 = 0 := by
    cases h : (decode (FetchDispatch.seed n l)).1 with
    | zero => rfl
    | succ k => cases k <;> simp [parse,h] at hcmd
  obtain ⟨nf,hf,sf⟩ := fetch_command n l s
  have sf' : CycleSteps exactSites nf (commandConfig 0 n l 0 s)
      (commandConfig 3911 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 s) := by
    simpa [parsedEntry,hk,Dispatch.target] using sf
  exact (cycle_prefix_halting_iff sf' (by simp [commandConfig])).mpr
    (shift_command_halts _ _ s hh)
#print axioms parsed_command_halts
end M6.Source

