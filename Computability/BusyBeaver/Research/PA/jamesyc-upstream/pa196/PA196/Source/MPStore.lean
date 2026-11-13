module
public import PA196.Source.MPField
public import PA196.Source.MPPush
public import PA196.Source.MPCopy
public import PA196.Source.MPCons
public import PA196.Source.MPGuard
/-! Arithmetic proof adapted from M6.Source.MPStore; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section
namespace PA196.Source.MP
open M6.Source

def registers (t w d h l : Nat) (f : Registers) : Registers := fun r =>
  if r = 1 then t else if r = 2 then w else if r = 4 then d else if r = 5 then h
  else if r = 8 then l else if r = 6 ∨ r = 7 then 0 else f r

def config (pc t w d h l : Nat) (f : Registers) : Configuration :=
  ⟨.at pc,registers t w d h l f⟩

theorem push_registers (t w d h l : Nat) (f : Registers) :
    AXPush.registers ⟨t,w,0,0,registers 0 0 d h l f⟩ = registers t w d h l f := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> by_cases h4 : r = 4 <;>
    by_cases h5 : r = 5 <;> by_cases h8 : r = 8 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [AXPush.registers,registers]

theorem field_registers (t w d h l : Nat) (f : Registers) :
    MPField.registers l d (registers t w 0 h 0 f) = registers t w d h l f := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> by_cases h4 : r = 4 <;>
    by_cases h5 : r = 5 <;> by_cases h8 : r = 8 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [MPField.registers,registers]

theorem copy_registers (t w d h l : Nat) (f : Registers) :
    CopyToT.registers 4 d t 0 (registers 0 w 0 h l f) = registers t w d h l f := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> by_cases h4 : r = 4 <;>
    by_cases h5 : r = 5 <;> by_cases h8 : r = 8 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [CopyToT.registers,registers]

theorem guard_registers (t w d h l : Nat) (f : Registers) :
    MPGuard.registers t h 0 (registers 0 w d 0 l f) = registers t w d h l f := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> by_cases h4 : r = 4 <;>
    by_cases h5 : r = 5 <;> by_cases h8 : r = 8 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [MPGuard.registers,registers]

end PA196.Source.MP

