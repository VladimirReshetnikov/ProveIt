module
public import M6.Source.AXMacroPlan
public import M6.Source.AXActualSpec
public import M6.Source.AXGate
@[expose] public section
namespace M6.Source.AXComposition

private theorem gate_registers (s : AXMacro.Store) (t a d h bottom : Nat) (f : Registers) :
    AXGate.registers ⟨t,a,d,h,0,0,AXMacro.registers s bottom f⟩ =
      AXMacro.registers {s with t := t,a := a,d := d,h := h} bottom f := by
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h3 : r=3 <;>
    by_cases h4 : r=4 <;> by_cases h5 : r=5 <;> by_cases h6 : r=6 <;>
    by_cases h7 : r=7 <;> by_cases h8 : r=8 <;>
    simp_all [AXGate.registers,AXMacro.registers]

theorem gate_effect (s : AXMacro.Store) (bottom : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (AXMacro.configAt 3769 s bottom f)
      (AXMacro.configAt 3910 {s with t := (if s.d=s.a ∨ s.h=s.a then 0 else s.t), a := 0, d := 0, h := 0} bottom f) := by
  obtain ⟨n,hn,hs⟩ := AXGate.gate s.t s.a s.d s.h (AXMacro.registers s bottom f)
  exact ⟨n,hn,by simpa only [AXGate.configAt,gate_registers,AXMacro.configAt] using hs⟩

/-- Composition interface. The explicit full Plan premise is discharged only by
checking every macro's primitive source binding; it is not a new axiom. -/
theorem full_effect
    (hp : AXMacro.Plan exactSites 25 3769 AXMacro.program)
    (t c d h y x tail bottom : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n
      (AXMacro.configAt 25 ⟨t,c,d,h,Cantor.pair y (Cantor.pair x tail),[]⟩ bottom f)
      (AXMacro.configAt 3910
        ⟨ActualAXCode.gate (d+x) (h+y) c,0,0,0,tail,
          ActualAXCode.pa135Heads (d+x) (h+y) c d h ++ [t]⟩ bottom f) := by
  obtain ⟨n,hn⟩ := hp.sound _ _ (AXSymbolic.macro_actual t c d h y x tail) bottom f
  obtain ⟨m,hm,hg⟩ := gate_effect
    ⟨ActualAXCode.bundle (d+x) (h+y) c,c,d+x,h+y,tail,
      ActualAXCode.pa135Heads (d+x) (h+y) c d h ++ [t]⟩ bottom f
  refine ⟨n+m,by omega,?_⟩
  simpa only [ActualAXCode.gate,eq_comm] using hn.append hg

#print axioms gate_effect
#print axioms full_effect
end M6.Source.AXComposition

