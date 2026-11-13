module
public import M6.Source.CommandRegisters
public import M6.Source.CyclicInvariant
@[expose] public section
namespace M6.Source
open Cantor Enumeration

theorem shift_command (n l : Nat) (s out : CommandStore)
    (he : commandEval .shift s = some out) :
    ∃ m, 0 < m ∧ CycleSteps exactSites m (commandConfig 3911 n l 0 s)
      (commandConfig 0 n l 0 out) := by
  rcases s with ⟨t,w,d,h⟩
  by_cases hh : t+h = 1
  · simp [commandEval,hh] at he
  · simp only [commandEval,hh,↓reduceIte,Option.some.injEq] at he
    subst out
    obtain ⟨m,hm,hbound,hs⟩ := S36Command.cyclic_normal_of_sum_ne_one t w h
      (commandRegisters n l 0 ⟨0,0,d,0⟩) hh
    refine ⟨m,hm,?_⟩
    simpa only [S36Command.start,command_s_registers,commandConfig] using hs

theorem mp_command (n tail x : Nat) (s out : CommandStore)
    (he : commandEval (.mp x) s = some out) :
    ∃ m, 0 < m ∧ CycleSteps exactSites m
      (commandConfig 3804 n (pair x tail) 0 s) (commandConfig 0 n tail 0 out) := by
  rcases s with ⟨t,w,d,h⟩
  obtain ⟨m,hm,hs⟩ := MP.command_field t w d h x tail (commandRegisters n 0 0 ⟨0,0,0,0⟩)
  have hc := nonexit_to_cycle hs (by simp [MP.config])
  by_cases hh : AXCode.wim t (d+x) = h
  all_goals
    simp only [commandEval,hh,↓reduceIte,Option.some.injEq] at he
    subst out
    refine ⟨m,hm,?_⟩
    simpa only [MP.config,command_mp_registers,hh,↓reduceIte,commandConfig] using hc

def parsedEntry (n l : Nat) (s : CommandStore) : Configuration :=
  let p := decode (FetchDispatch.seed n l)
  commandConfig (Dispatch.target p.1) (FetchDispatch.nextN n l) p.2 (p.1-2) s

theorem fetch_command (n l : Nat) (s : CommandStore) :
    ∃ m, 0 < m ∧ CycleSteps exactSites m (commandConfig 0 n l 0 s) (parsedEntry n l s) := by
  obtain ⟨m,hm,hs⟩ := FetchDispatch.total n l (commandRegisters 0 0 0 s)
  have hc := nonexit_to_cycle hs (by simp [FetchDispatch.commandEntry])
  exact ⟨m,hm,by simpa only [Fetch.start,FetchDispatch.commandEntry,command_fetch_registers,
    parsedEntry,commandConfig] using hc⟩

#print axioms shift_command
#print axioms mp_command
#print axioms fetch_command
end M6.Source

