import PA194CommandRegisters
import M6.Source.CyclicInvariant
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194CommandTransfer
open M6.Source M6.Source.Cantor PA196 PA194CommandRegisters PA194MPSource PA194ShiftSource

def step : Commands.Command → Commands.Store → Option Commands.Store
  | .shift, s =>
      if s.t + s.h = 1 then none
      else some ⟨s.h, (decode s.w).2, s.d, (decode s.w).1⟩
  | .mp x, s =>
      let y := s.d + x
      if Commands.Code.I s.t y = s.h then some ⟨y, pair 0 s.w, y, 0⟩
      else some ⟨0, s.w, y, 0⟩
  | .ax c x y, s =>
      some ⟨PA194AXReadable.guardedOldBundle (s.h + y) (s.d + x) c,
        ([PA194AXSymbolic.diagonal c] ++ Commands.Code.heads (s.d + x) (s.h + y) c s.d s.h ++ [s.t]).foldr pair s.w, 0, 0⟩

theorem shift_command (n l : Nat) (s out : Commands.Store)
    (he : step .shift s = some out) :
    ∃ m, 0<m ∧ CycleSteps PA194SourceProgram.sites m (commandConfig 3661 n l 0 s)
      (commandConfig 25 n l 0 out) := by
  rcases s with ⟨t,w,d,h⟩
  by_cases hh : t+h=1
  · simp [step,hh] at he
  · simp only [step,hh,↓reduceIte,Option.some.injEq] at he
    subst out
    obtain ⟨m,hm,hs⟩ := ShiftCommand.cyclic_normal_of_sum_ne_one t w h
      (commandRegisters n l 0 ⟨0,0,d,0⟩) hh
    refine ⟨m,hm,?_⟩
    simpa only [ShiftCommand.start,ShiftCommand.normal,command_shift_registers,commandConfig] using hs

private theorem wim_eq (a b : Nat) : AXCode.wim a b = Commands.Code.I a b := rfl

theorem mp_command (n tail x : Nat) (s out : Commands.Store)
    (he : step (.mp x) s = some out) :
    ∃ m, 0<m ∧ CycleSteps PA194SourceProgram.sites m
      (commandConfig 3554 n (pair x tail) 0 s) (commandConfig 25 n tail 0 out) := by
  rcases s with ⟨t,w,d,h⟩
  obtain ⟨m,hm,hs⟩ := MP.command_field t w d h x tail (commandRegisters n 0 0 ⟨0,0,0,0⟩)
  have hc := nonexit_to_cycle hs (by simp [MP.config])
  by_cases hh : AXCode.wim t (d+x)=h
  all_goals
    simp only [step,← wim_eq,hh,↓reduceIte,Option.some.injEq] at he
    subst out
    refine ⟨m,hm,?_⟩
    simpa only [MP.config,command_mp_registers,hh,↓reduceIte,commandConfig] using hc

theorem ax_command (n tail c x y : Nat) (s out : Commands.Store)
    (he : step (.ax c x y) s = some out) :
    ∃ m, 0<m ∧ CycleSteps PA194SourceProgram.sites m
      (commandConfig 50 n (pair y (pair x tail)) c s)
      (commandConfig 25 n tail 0 out) := by
  rcases s with ⟨t,w,d,h⟩
  simp only [step,Option.some.injEq] at he
  subst out
  obtain ⟨m,hs⟩ := PA194AXReadable.complete t c d h y x tail w
    (commandRegisters n 0 0 ⟨0,0,0,0⟩)
  have hc := nonexit_to_cycle hs (by simp [AXMacro.configAt])
  have hbody : CycleSteps PA194SourceProgram.sites m
      (commandConfig 50 n (pair y (pair x tail)) c ⟨t,w,d,h⟩)
      (commandConfig 3660 n tail 0
        ⟨PA194AXReadable.guardedOldBundle (h+y) (d+x) c,
          ([PA194AXSymbolic.diagonal c] ++ Commands.Code.heads (d+x) (h+y) c d h ++ [t]).foldr pair w,0,0⟩) := by
    simpa only [AXMacro.configAt,command_ax_registers,AXCode.stackCode,List.foldr_nil,
      commandConfig] using hc
  exact ⟨m+1,by omega,hbody.append (command_return n tail _)⟩

#print axioms shift_command
#print axioms mp_command
#print axioms ax_command
end PA194CommandTransfer
