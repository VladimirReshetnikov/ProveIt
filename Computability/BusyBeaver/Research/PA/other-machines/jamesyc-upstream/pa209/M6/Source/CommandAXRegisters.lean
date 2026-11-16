module
public import M6.Source.CommandSMP
public import M6.Source.AXMacro
@[expose] public section
namespace M6.Source

theorem command_ax_registers (n l a t d h bottom : Nat) (stack : List Nat) :
    AXMacro.registers ⟨t,a,d,h,l,stack⟩ bottom (commandRegisters n 0 0 ⟨0,0,0,0⟩) =
      commandRegisters n l a ⟨t,AXCode.stackCode stack bottom,d,h⟩ := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem command_return (n l : Nat) (s : CommandStore) :
    CycleSteps exactSites 1 (commandConfig 3910 n l 0 s) (commandConfig 0 n l 0 s) := by
  rcases s with ⟨t,w,d,h⟩
  have hr := MP.return_to_root t w d h l (commandRegisters n 0 0 ⟨0,0,0,0⟩)
  have hc := nonexit_to_cycle hr (by simp [MP.config])
  simpa only [MP.config,command_mp_registers,commandConfig] using hc
end M6.Source

