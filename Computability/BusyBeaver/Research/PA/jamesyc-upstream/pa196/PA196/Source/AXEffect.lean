module
public import PA196.Source.AXFullPlan
public import PA196.Source.AXSymbolic
public import PA196.Source.AXGate
public import PA196.Commands.Store
@[expose] public section
namespace PA196.Source.AXEffect
open M6.Source

private theorem gate_registers (s : AXMacro.Store) (t a d h bottom : Nat) (f : Registers) :
    AXGate.registers ⟨t,a,d,h,0,0,AXMacro.registers s bottom f⟩ =
      AXMacro.registers {s with t := t,a := a,d := d,h := h} bottom f := by
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
    by_cases h4 : r=4 <;> by_cases h5 : r=5 <;> by_cases h6 : r=6 <;>
    by_cases h7 : r=7 <;> by_cases h8 : r=8 <;>
    simp_all [AXGate.registers,AXMacro.registers]

theorem gate_effect (s : AXMacro.Store) (bottom : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps Program.sites n (AXMacro.configAt 3658 s bottom f)
      (AXMacro.configAt 3799
        {s with t := (if s.d=s.a ∨ s.h=s.a then 0 else s.t), a := 0, d := 0, h := 0}
        bottom f) := by
  obtain ⟨n,hn,hs⟩ := AXGate.gate s.t s.a s.d s.h (AXMacro.registers s bottom f)
  exact ⟨n,hn,by simpa only [AXGate.configAt,gate_registers,AXMacro.configAt] using hs⟩

/-- The complete new AX body, uniformly for every natural input and stack
bottom. All 264 arithmetic macros and all guard rows are bound to PA196.Program. -/
theorem full_effect (t c d h y x tail bottom : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps Program.sites n
      (AXMacro.configAt 50 ⟨t,c,d,h,Cantor.pair y (Cantor.pair x tail),[]⟩ bottom f)
      (AXMacro.configAt 3799
        ⟨Commands.Code.gate (h+y) (d+x) c,0,0,0,tail,
          Commands.Code.heads (d+x) (h+y) c d h ++ [t]⟩ bottom f) := by
  obtain ⟨n,hn⟩ := AXBindings.full_plan.sound _ _
    (AXSymbolic.macro_result t c d h y x tail) bottom f
  obtain ⟨m,hm,hg⟩ := gate_effect
    ⟨Commands.Code.bundle (h+y) (d+x) c,c,d+x,h+y,tail,
      Commands.Code.heads (d+x) (h+y) c d h ++ [t]⟩ bottom f
  refine ⟨n+m,by omega,?_⟩
  simpa only [Commands.Code.gate,eq_comm,or_comm] using hn.append hg

#print axioms full_effect
end PA196.Source.AXEffect
