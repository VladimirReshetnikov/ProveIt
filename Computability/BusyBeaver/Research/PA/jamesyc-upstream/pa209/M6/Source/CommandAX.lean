module
public import M6.Source.CommandAXRegisters
public import M6.Source.AXCommand
@[expose] public section
namespace M6.Source
open Cantor Enumeration

/-- The actual full AX macro on the common arithmetic command boundary state. -/
theorem ax_command (n tail c x y : Nat) (s out : CommandStore)
    (he : commandEval (.ax c x y) s = some out) :
    ∃ m, 0 < m ∧ CycleSteps exactSites m
      (commandConfig 25 n (pair y (pair x tail)) c s)
      (commandConfig 0 n tail 0 out) := by
  rcases s with ⟨t,w,d,h⟩
  simp only [commandEval,Option.some.injEq] at he
  subst out
  obtain ⟨m,hm,hs⟩ := AXCommand.encoded t c d h y x tail w
    (commandRegisters n 0 0 ⟨0,0,0,0⟩)
  have hc := nonexit_to_cycle hs (by simp [AXMacro.configAt])
  have hbody : CycleSteps exactSites m
      (commandConfig 25 n (pair y (pair x tail)) c ⟨t,w,d,h⟩)
      (commandConfig 3910 n tail 0
        ⟨ActualAXCode.gate (d+x) (h+y) c,
          (ActualAXCode.pa135Heads (d+x) (h+y) c d h ++ [t]).foldr pair w,0,0⟩) := by
    simpa only [AXMacro.configAt,command_ax_registers,AXCode.stackCode,List.foldr_nil,
      commandConfig] using hc
  exact ⟨m+1,by omega,hbody.append (command_return n tail _)⟩
#print axioms ax_command
end M6.Source

