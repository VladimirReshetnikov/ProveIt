import PA194AXPlan
import PA194AXGate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194AXComplete
open M6.Source PA194SourceProgram PA194AXSymbolic PA196.Commands.Code

def endStore (t c d h y x tail : Nat) : AXMacro.Store :=
  ⟨oldBundle (h+y) (d+x) c,c,d+x,h+y,tail,
    [diagonal c] ++ heads (d+x) (h+y) c d h ++ [t]⟩

theorem middle_eq (t c d h y x tail bottom : Nat) (f : Registers) :
    AXMacro.configAt 3519 (endStore t c d h y x tail) bottom f =
      PA194AXGate.configAt 3519
        ⟨oldBundle (h+y) (d+x) c,c,d+x,h+y,0,0,
          AXMacro.registers (endStore t c d h y x tail) bottom f⟩ := by
  simp only [AXMacro.configAt, PA194AXGate.configAt, Configuration.mk.injEq, true_and]
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
    by_cases h4 : r=4 <;> by_cases h5 : r=5 <;> by_cases h6 : r=6 <;>
    by_cases h7 : r=7 <;> by_cases h8 : r=8 <;>
    simp_all [AXMacro.registers, PA194AXGate.registers, endStore]

theorem complete (t c d h y x tail bottom : Nat) (f : Registers) :
    ∃ n, Steps sites n
      (AXMacro.configAt 50 ⟨t,c,d,h,Cantor.pair y (Cantor.pair x tail),[]⟩ bottom f)
      (PA194AXGate.configAt 3660
        ⟨if d+x=c ∨ h+y=c then 0 else oldBundle (h+y) (d+x) c,0,0,0,0,0,
          AXMacro.registers (endStore t c d h y x tail) bottom f⟩) := by
  obtain ⟨n,hn⟩ := PA194AXPlan.source_core t c d h y x tail bottom f
  obtain ⟨m,_,hm⟩ := PA194AXGate.gate (oldBundle (h+y) (d+x) c) c (d+x) (h+y)
    (AXMacro.registers (endStore t c d h y x tail) bottom f)
  rw [←middle_eq] at hm
  exact ⟨n+m,hn.append hm⟩

#print axioms middle_eq
#print axioms complete
end PA194AXComplete
