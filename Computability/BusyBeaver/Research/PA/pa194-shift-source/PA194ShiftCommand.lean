import PA194NIPGuard
import PA194StackDecode
import M6.Source.NonexitCycle
namespace PA194ShiftSource.ShiftCommand
open M6.Source

def registers (t w h : Nat) (f : Registers) : Registers :=
  Unpair.registers ⟨w,h,0,0,write f 1 t⟩

def start (t w h : Nat) (f : Registers) : Configuration :=
  ⟨.at 3661,registers t w h f⟩

def normal (t w h : Nat) (f : Registers) : Configuration :=
  ⟨.at 25,registers t w h f⟩

def halted (t w h : Nat) (f : Registers) : Configuration :=
  ⟨.halted,registers t w h f⟩

private theorem register_bridge (t w h x y : Nat) (f : Registers) :
    S36Lift.registers ⟨t,h,x,Unpair.registers ⟨w,0,0,y,f⟩⟩ =
      Unpair.registers ⟨w,h,x,y,write f 1 t⟩ := by
  funext r
  by_cases h1 : r=1 <;> by_cases h2 : r=2 <;> by_cases h5 : r=5 <;>
    by_cases h6 : r=6 <;> by_cases h7 : r=7 <;>
    simp_all [S36Lift.registers,Unpair.registers,write]

theorem halt_of_sum_one (t w h : Nat) (f : Registers) (hs : t+h=1) :
    Steps PA194SourceProgram.sites (6*t+7*h+11) (start t w h f) (halted h w 0 f) := by
  have q := NIPGuard.s36_halts_of_sum_one t h (Unpair.registers ⟨w,0,0,0,f⟩) hs
  simpa only [NIPGuard.configAt,register_bridge,start,halted,registers] using q

/-- Exact PA194 Shift, including its extra root-wrap jump and stack decoder. -/
theorem normal_of_sum_ne_one (t w h : Nat) (f : Registers) (hs : t+h≠1) :
    ∃ n, 0<n ∧ Steps PA194SourceProgram.sites n (start t w h f)
      (normal h (Cantor.decode w).2 (Cantor.decode w).1 f) := by
  have before := NIPGuard.s36_reaches_stack_of_sum_ne_one t h
    (Unpair.registers ⟨w,0,0,0,f⟩) hs
  simp only [NIPGuard.configAt,register_bridge] at before
  obtain ⟨m,hm,after⟩ := PA194StackDecode.unpair w (write f 1 h)
  exact ⟨8*t+9*h+10+m,by omega,before.append after⟩

theorem cyclic_normal_of_sum_ne_one (t w h : Nat) (f : Registers) (hs : t+h≠1) :
    ∃ n, 0<n ∧ CycleSteps PA194SourceProgram.sites n (start t w h f)
      (normal h (Cantor.decode w).2 (Cantor.decode w).1 f) := by
  obtain ⟨n,hn,hstep⟩ := normal_of_sum_ne_one t w h f hs
  exact ⟨n,hn,nonexit_to_cycle hstep (by simp [normal])⟩

#print axioms halt_of_sum_one
#print axioms cyclic_normal_of_sum_ne_one
end PA194ShiftSource.ShiftCommand
