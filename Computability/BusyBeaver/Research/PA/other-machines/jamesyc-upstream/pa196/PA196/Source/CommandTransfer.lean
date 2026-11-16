module
public import PA196.Source.CommandRegisters
@[expose] public section
namespace PA196.Source
open M6.Source Cantor

theorem shift_command (n l : Nat) (s out : Commands.Store)
    (he : Commands.step .shift s = some out) :
    ∃ m, 0<m ∧ CycleSteps Program.sites m (commandConfig 3800 n l 0 s)
      (commandConfig 25 n l 0 out) := by
  rcases s with ⟨t,w,d,h⟩
  by_cases hh : t+h=1
  · simp [Commands.step,hh] at he
  · simp only [Commands.step,hh,↓reduceIte,Option.some.injEq] at he
    subst out
    obtain ⟨m,hm,hs⟩ := ShiftCommand.cyclic_normal_of_sum_ne_one t w h
      (commandRegisters n l 0 ⟨0,0,d,0⟩) hh
    refine ⟨m,hm,?_⟩
    simpa only [ShiftCommand.start,ShiftCommand.normal,command_shift_registers,commandConfig] using hs

private theorem wim_eq (a b : Nat) : AXCode.wim a b = Commands.Code.I a b := rfl

theorem mp_command (n tail x : Nat) (s out : Commands.Store)
    (he : Commands.step (.mp x) s = some out) :
    ∃ m, 0<m ∧ CycleSteps Program.sites m
      (commandConfig 3693 n (pair x tail) 0 s) (commandConfig 25 n tail 0 out) := by
  rcases s with ⟨t,w,d,h⟩
  obtain ⟨m,hm,hs⟩ := MP.command_field t w d h x tail (commandRegisters n 0 0 ⟨0,0,0,0⟩)
  have hc := nonexit_to_cycle hs (by simp [MP.config])
  by_cases hh : AXCode.wim t (d+x)=h
  all_goals
    simp only [Commands.step,← wim_eq,hh,↓reduceIte,Option.some.injEq] at he
    subst out
    refine ⟨m,hm,?_⟩
    simpa only [MP.config,command_mp_registers,hh,↓reduceIte,commandConfig] using hc

/-- The 201-token PA196 AX body implements the new eight-head command profile. -/
theorem ax_command (n tail c x y : Nat) (s out : Commands.Store)
    (he : Commands.step (.ax c x y) s = some out) :
    ∃ m, 0<m ∧ CycleSteps Program.sites m
      (commandConfig 50 n (pair y (pair x tail)) c s)
      (commandConfig 25 n tail 0 out) := by
  rcases s with ⟨t,w,d,h⟩
  simp only [Commands.step,Option.some.injEq] at he
  subst out
  obtain ⟨m,hm,hs⟩ := AXEffect.full_effect t c d h y x tail w
    (commandRegisters n 0 0 ⟨0,0,0,0⟩)
  have hc := nonexit_to_cycle hs (by simp [AXMacro.configAt])
  have hbody : CycleSteps Program.sites m
      (commandConfig 50 n (pair y (pair x tail)) c ⟨t,w,d,h⟩)
      (commandConfig 3799 n tail 0
        ⟨Commands.Code.gate (h+y) (d+x) c,
          (Commands.Code.heads (d+x) (h+y) c d h ++ [t]).foldr pair w,0,0⟩) := by
    simpa only [AXMacro.configAt,command_ax_registers,AXCode.stackCode,List.foldr_nil,
      commandConfig] using hc
  exact ⟨m+1,by omega,hbody.append (command_return n tail _)⟩

structure Parsed where
  command : Commands.Command
  next : Nat

def parse (n : Nat) : Parsed :=
  let p := decode n
  match p.1 with
  | 0 => ⟨.shift,p.2⟩
  | 1 => let q := decode p.2; ⟨.mp q.1,q.2⟩
  | c+2 => let q := decode p.2; let r := decode q.2; ⟨.ax c r.1 q.1,r.2⟩

def parsedEntry (n l : Nat) (s : Commands.Store) : Configuration :=
  let p := decode (FetchDispatch.seed n l)
  commandConfig (Dispatch.target p.1) (FetchDispatch.nextN n l) p.2 (p.1-2) s

theorem fetch_command (n l : Nat) (s : Commands.Store) :
    ∃ m, 0<m ∧ CycleSteps Program.sites m (commandConfig 25 n l 0 s) (parsedEntry n l s) := by
  obtain ⟨m,hm,hs⟩ := FetchDispatch.total n l (commandRegisters 0 0 0 s)
  have hc := nonexit_to_cycle hs (by simp [FetchDispatch.commandEntry])
  exact ⟨m,hm,by simpa only [Fetch.start,FetchDispatch.commandEntry,command_fetch_registers,
    parsedEntry,commandConfig] using hc⟩

/-- Exact source fetch, parsing, operand consumption, command execution, and
return to fetch. Every case is bound to the PA196 program's physical rows. -/
theorem parsed_command_step (n l : Nat) (s out : Commands.Store)
    (he : Commands.step (parse (FetchDispatch.seed n l)).command s = some out) :
    ∃ m, 0<m ∧ CycleSteps Program.sites m (commandConfig 25 n l 0 s)
      (commandConfig 25 (FetchDispatch.nextN n l) (parse (FetchDispatch.seed n l)).next 0 out) := by
  obtain ⟨nf,hf,sf⟩ := fetch_command n l s
  cases hk : (decode (FetchDispatch.seed n l)).1 with
  | zero =>
    have he' : Commands.step .shift s = some out := by simpa only [parse,hk] using he
    obtain ⟨ns,hs,ss⟩ := shift_command (FetchDispatch.nextN n l)
      (decode (FetchDispatch.seed n l)).2 s out he'
    have sf' : CycleSteps Program.sites nf (commandConfig 25 n l 0 s)
        (commandConfig 3800 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 s) := by
      simpa [parsedEntry,hk,Dispatch.target] using sf
    exact ⟨nf+ns,by omega,by simpa only [parse,hk] using sf'.append ss⟩
  | succ k =>
    cases k with
    | zero =>
      have he' : Commands.step (.mp (decode (decode (FetchDispatch.seed n l)).2).1) s = some out := by
        simpa only [parse,hk] using he
      obtain ⟨ns,hs,ss⟩ := mp_command (FetchDispatch.nextN n l)
        (decode (decode (FetchDispatch.seed n l)).2).2
        (decode (decode (FetchDispatch.seed n l)).2).1 s out he'
      rw [pair_decode] at ss
      have sf' : CycleSteps Program.sites nf (commandConfig 25 n l 0 s)
          (commandConfig 3693 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 s) := by
        simpa [parsedEntry,hk,Dispatch.target] using sf
      exact ⟨nf+ns,by omega,by simpa only [parse,hk] using sf'.append ss⟩
    | succ c =>
      have he' : Commands.step (.ax c
          (decode (decode (decode (FetchDispatch.seed n l)).2).2).1
          (decode (decode (FetchDispatch.seed n l)).2).1) s = some out := by
        simpa only [parse,hk] using he
      obtain ⟨ns,hs,ss⟩ := ax_command (FetchDispatch.nextN n l)
        (decode (decode (decode (FetchDispatch.seed n l)).2).2).2 c
        (decode (decode (decode (FetchDispatch.seed n l)).2).2).1
        (decode (decode (FetchDispatch.seed n l)).2).1 s out he'
      rw [pair_decode,pair_decode] at ss
      have sf' : CycleSteps Program.sites nf (commandConfig 25 n l 0 s)
          (commandConfig 50 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 c s) := by
        simpa [parsedEntry,hk,Dispatch.target,Nat.add_assoc] using sf
      exact ⟨nf+ns,by omega,by simpa only [parse,hk] using sf'.append ss⟩

#print axioms shift_command
#print axioms mp_command
#print axioms ax_command
#print axioms parsed_command_step
end PA196.Source
