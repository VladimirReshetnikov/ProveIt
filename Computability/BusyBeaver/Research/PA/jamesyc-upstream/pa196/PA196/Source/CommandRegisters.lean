module
public import PA196.Commands.Store
public import PA196.Source.MPCommand
public import PA196.Source.ShiftCommand
public import PA196.Source.FetchDispatch
public import PA196.Source.AXEffect
public import M6.Source.CyclicInvariant
@[expose] public section
namespace PA196.Source
open M6.Source

def commandRegisters (n l a : Nat) (s : Commands.Store) : Registers :=
  fun r => [n,s.t,s.w,a,s.d,s.h,0,0,l].getD r.val 0

def commandConfig (pc n l a : Nat) (s : Commands.Store) : Configuration :=
  ⟨.at pc,commandRegisters n l a s⟩

theorem command_mp_registers (n l a t w d h : Nat) :
    MP.registers t w d h l (commandRegisters n 0 a ⟨0,0,0,0⟩) =
      commandRegisters n l a ⟨t,w,d,h⟩ := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem command_shift_registers (n l a t w d h : Nat) :
    ShiftCommand.registers t w h (commandRegisters n l a ⟨0,0,d,0⟩) =
      commandRegisters n l a ⟨t,w,d,h⟩ := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem command_fetch_registers (n l a : Nat) (s : Commands.Store) :
    Fetch.registers n l a (commandRegisters 0 0 0 s) = commandRegisters n l a s := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem command_ax_registers (n l a t d h bottom : Nat) (stack : List Nat) :
    AXMacro.registers ⟨t,a,d,h,l,stack⟩ bottom (commandRegisters n 0 0 ⟨0,0,0,0⟩) =
      commandRegisters n l a ⟨t,AXCode.stackCode stack bottom,d,h⟩ := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem command_return (n l : Nat) (s : Commands.Store) :
    CycleSteps Program.sites 1 (commandConfig 3799 n l 0 s) (commandConfig 25 n l 0 s) := by
  rcases s with ⟨t,w,d,h⟩
  have hr := MP.return_to_root t w d h l (commandRegisters n 0 0 ⟨0,0,0,0⟩)
  have hc := nonexit_to_cycle hr (by simp [MP.config])
  simpa only [MP.config,command_mp_registers,commandConfig] using hc

end PA196.Source
