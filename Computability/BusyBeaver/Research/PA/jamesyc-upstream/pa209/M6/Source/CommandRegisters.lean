module
public import M6.Source.CommandStore
public import M6.Source.MPCyclic
public import M6.Source.S36Cyclic
public import M6.Source.FetchDispatch
@[expose] public section
namespace M6.Source

theorem command_mp_registers (n l a t w d h : Nat) :
    MP.registers t w d h l (commandRegisters n 0 a ⟨0,0,0,0⟩) =
      commandRegisters n l a ⟨t,w,d,h⟩ := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem command_s_registers (n l a t w d h : Nat) :
    S36Command.registers t w h (commandRegisters n l a ⟨0,0,d,0⟩) =
      commandRegisters n l a ⟨t,w,d,h⟩ := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem command_fetch_registers (n l a : Nat) (s : CommandStore) :
    Fetch.registers n l a (commandRegisters 0 0 0 s) = commandRegisters n l a s := by
  funext ⟨r,hr⟩
  have hc : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end M6.Source

