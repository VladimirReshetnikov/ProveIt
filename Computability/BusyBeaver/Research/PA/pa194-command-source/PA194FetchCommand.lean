import PA194CommandTransfer
import PA194FetchDispatch
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194FetchCommand
open M6.Source M6.Source.Cantor PA196 PA194CommandRegisters PA194CommandTransfer PA194FetchSource

theorem command_fetch_registers (n l a : Nat) (s : Commands.Store) :
    Fetch.registers n l a (commandRegisters 0 0 0 s) = commandRegisters n l a s := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

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
    ∃ m, 0<m ∧ CycleSteps PA194SourceProgram.sites m (commandConfig 25 n l 0 s) (parsedEntry n l s) := by
  obtain ⟨m,hm,hs⟩ := FetchDispatch.total n l (commandRegisters 0 0 0 s)
  have hc := nonexit_to_cycle hs (by simp [FetchDispatch.commandEntry])
  exact ⟨m,hm,by simpa only [Fetch.start,FetchDispatch.commandEntry,command_fetch_registers,
    parsedEntry,commandConfig] using hc⟩

/-- Exact source fetch, parsing, operand consumption, command execution, and
return to fetch. Every case is bound to the PA194 program's physical rows. -/
theorem parsed_command_step (n l : Nat) (s out : Commands.Store)
    (he : PA194CommandTransfer.step (parse (FetchDispatch.seed n l)).command s = some out) :
    ∃ m, 0<m ∧ CycleSteps PA194SourceProgram.sites m (commandConfig 25 n l 0 s)
      (commandConfig 25 (FetchDispatch.nextN n l) (parse (FetchDispatch.seed n l)).next 0 out) := by
  obtain ⟨nf,hf,sf⟩ := fetch_command n l s
  cases hk : (decode (FetchDispatch.seed n l)).1 with
  | zero =>
    have he' : PA194CommandTransfer.step .shift s = some out := by simpa only [parse,hk] using he
    obtain ⟨ns,hs,ss⟩ := shift_command (FetchDispatch.nextN n l)
      (decode (FetchDispatch.seed n l)).2 s out he'
    have sf' : CycleSteps PA194SourceProgram.sites nf (commandConfig 25 n l 0 s)
        (commandConfig 3661 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 s) := by
      simpa [parsedEntry,hk,Dispatch.target] using sf
    exact ⟨nf+ns,by omega,by simpa only [parse,hk] using sf'.append ss⟩
  | succ k =>
    cases k with
    | zero =>
      have he' : PA194CommandTransfer.step (.mp (decode (decode (FetchDispatch.seed n l)).2).1) s = some out := by
        simpa only [parse,hk] using he
      obtain ⟨ns,hs,ss⟩ := mp_command (FetchDispatch.nextN n l)
        (decode (decode (FetchDispatch.seed n l)).2).2
        (decode (decode (FetchDispatch.seed n l)).2).1 s out he'
      rw [pair_decode] at ss
      have sf' : CycleSteps PA194SourceProgram.sites nf (commandConfig 25 n l 0 s)
          (commandConfig 3554 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 s) := by
        simpa [parsedEntry,hk,Dispatch.target] using sf
      exact ⟨nf+ns,by omega,by simpa only [parse,hk] using sf'.append ss⟩
    | succ c =>
      have he' : PA194CommandTransfer.step (.ax c
          (decode (decode (decode (FetchDispatch.seed n l)).2).2).1
          (decode (decode (FetchDispatch.seed n l)).2).1) s = some out := by
        simpa only [parse,hk] using he
      obtain ⟨ns,hs,ss⟩ := ax_command (FetchDispatch.nextN n l)
        (decode (decode (decode (FetchDispatch.seed n l)).2).2).2 c
        (decode (decode (decode (FetchDispatch.seed n l)).2).2).1
        (decode (decode (FetchDispatch.seed n l)).2).1 s out he'
      rw [pair_decode,pair_decode] at ss
      have sf' : CycleSteps PA194SourceProgram.sites nf (commandConfig 25 n l 0 s)
          (commandConfig 50 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 c s) := by
        simpa [parsedEntry,hk,Dispatch.target,Nat.add_assoc] using sf
      exact ⟨nf+ns,by omega,by simpa only [parse,hk] using sf'.append ss⟩



/-- If the parsed command halts, source execution reaches its explicit halt. -/
theorem parsed_command_halts (n l : Nat) (s : Commands.Store)
    (he : PA194CommandTransfer.step (parse (FetchDispatch.seed n l)).command s = none) :
    ∃ m, 0<m ∧ CycleSteps PA194SourceProgram.sites m (commandConfig 25 n l 0 s)
      ⟨.halted, commandRegisters (FetchDispatch.nextN n l)
        (decode (FetchDispatch.seed n l)).2 0 ⟨s.h,s.w,s.d,0⟩⟩ := by
  obtain ⟨nf,hf,sf⟩ := fetch_command n l s
  cases hk : (decode (FetchDispatch.seed n l)).1 with
  | zero =>
    have he' : PA194CommandTransfer.step .shift s = none := by simpa only [parse,hk] using he
    rcases s with ⟨t,w,d,h⟩
    have hh : t+h=1 := by
      by_cases hn : t+h=1
      · exact hn
      · simp [PA194CommandTransfer.step,hn] at he'
    have hs := PA194ShiftSource.ShiftCommand.halt_of_sum_one t w h
      (commandRegisters (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 ⟨0,0,d,0⟩) hh
    have hc := nonexit_to_cycle hs (by simp [PA194ShiftSource.ShiftCommand.halted])
    have sf' : CycleSteps PA194SourceProgram.sites nf (commandConfig 25 n l 0 ⟨t,w,d,h⟩)
        (commandConfig 3661 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 ⟨t,w,d,h⟩) := by
      simpa [parsedEntry,hk,Dispatch.target] using sf
    have hc' : CycleSteps PA194SourceProgram.sites (6*t+7*h+11)
        (commandConfig 3661 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 ⟨t,w,d,h⟩)
        ⟨.halted,commandRegisters (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 ⟨h,w,d,0⟩⟩ := by
      simpa only [PA194ShiftSource.ShiftCommand.start, PA194ShiftSource.ShiftCommand.halted,
        command_shift_registers,commandConfig] using hc
    exact ⟨nf+(6*t+7*h+11),by omega,sf'.append hc'⟩
  | succ k =>
    cases k with
    | zero =>
      simp [parse,hk,PA194CommandTransfer.step] at he
      split at he <;> simp_all
    | succ c =>
      simp [parse,hk,PA194CommandTransfer.step] at he

#print axioms parsed_command_halts

#print axioms fetch_command
#print axioms parsed_command_step
end PA194FetchCommand
