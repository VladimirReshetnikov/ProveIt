import PA194AXComplete
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PA194AXReadable
open M6.Source PA194SourceProgram PA194AXSymbolic PA194AXComplete PA196.Commands.Code

def guardedOldBundle (a b c : Nat) : Nat :=
  if b=c ∨ a=c then 0 else oldBundle a b c

theorem final_config (t c d h y x tail bottom : Nat) (f : Registers) :
    PA194AXGate.configAt 3660
      ⟨if d+x=c ∨ h+y=c then 0 else oldBundle (h+y) (d+x) c,0,0,0,0,0,
        AXMacro.registers (endStore t c d h y x tail) bottom f⟩ =
    AXMacro.configAt 3660
      ⟨guardedOldBundle (h+y) (d+x) c,0,0,0,tail,
        [diagonal c] ++ heads (d+x) (h+y) c d h ++ [t]⟩ bottom f := by
  simp only [PA194AXGate.configAt,AXMacro.configAt,Configuration.mk.injEq,true_and]
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
    by_cases h4 : r=4 <;> by_cases h5 : r=5 <;> by_cases h6 : r=6 <;>
    by_cases h7 : r=7 <;> by_cases h8 : r=8 <;>
    simp_all [AXMacro.registers, PA194AXGate.registers, endStore, guardedOldBundle]

theorem complete (t c d h y x tail bottom : Nat) (f : Registers) :
    ∃ n, Steps sites n
      (AXMacro.configAt 50 ⟨t,c,d,h,Cantor.pair y (Cantor.pair x tail),[]⟩ bottom f)
      (AXMacro.configAt 3660
        ⟨guardedOldBundle (h+y) (d+x) c,0,0,0,tail,
          [diagonal c] ++ heads (d+x) (h+y) c d h ++ [t]⟩ bottom f) := by
  obtain ⟨n,hn⟩ := PA194AXComplete.complete t c d h y x tail bottom f
  exact ⟨n, (final_config t c d h y x tail bottom f) ▸ hn⟩

#print axioms complete
end PA194AXReadable
