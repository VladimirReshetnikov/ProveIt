module
public import M6.Source.Semantics
public import M6.Source.ExactSource
@[expose] public section
set_option linter.unusedSimpArgs false
namespace M6.Source.AXGateCompare
structure Store where
  t : Nat
  h : Nat
  x : Nat
  frame : Registers
def registers (s : Store) : Registers := fun r =>
  if r = 1 then s.t else if r = 5 then s.h else if r = 6 then s.x else s.frame r
def configAt (base pc : Nat) (s : Store) : Configuration := ⟨.at (base+pc),registers s⟩
def expected (base : Nat) : Nat → Instruction
  | 0 => .dec 5 (some (base+4)) (some (base+1))
  | 1 => .dec 6 (some (base+3)) (some (base+2))
  | 2 => .jump (some (base+0))
  | 3 => .jump (some (base+5))
  | 4 => .dec 6 (some (base+10)) (some (base+5))
  | 5 => .dec 5 (some (base+7)) (some (base+6))
  | 6 => .jump (some (base+5))
  | 7 => .dec 6 (some (base+9)) (some (base+8))
  | 8 => .jump (some (base+5))
  | 9 => .jump (some (base+12))
  | 10 => .dec 1 (some (base+12)) (some (base+11))
  | 11 => .jump (some (base+10))
  | _ => .halt
def Bound (sites : Array Site) (base : Nat) : Prop :=
  ∀ j : Fin 12, resolveAt sites (base+j.val) = some (expected base j.val)
variable {sites : Array Site} {base : Nat} (hbound : Bound sites base)
private theorem write_t (s : Store) (v : Nat) :
    write (registers s) 1 v = registers {s with t := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;>
    simp_all [write,registers]
private theorem write_h (s : Store) (v : Nat) :
    write (registers s) 5 v = registers {s with h := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;>
    simp_all [write,registers]
private theorem write_x (s : Store) (v : Nat) :
    write (registers s) 6 v = registers {s with x := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;>
    simp_all [write,registers]
include hbound
theorem step_0 (t h x : Nat) (f : Registers) :
    step sites (configAt base 0 ⟨t,h,x,f⟩) = if h = 0 then configAt base 4 ⟨t,h,x,f⟩ else configAt base 1 ⟨t,h-1,x,f⟩ := by
  change step sites ⟨.at (base+0),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+0) = some (expected base 0) := hbound ⟨0,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : h = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_1 (t h x : Nat) (f : Registers) :
    step sites (configAt base 1 ⟨t,h,x,f⟩) = if x = 0 then configAt base 3 ⟨t,h,x,f⟩ else configAt base 2 ⟨t,h,x-1,f⟩ := by
  change step sites ⟨.at (base+1),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+1) = some (expected base 1) := hbound ⟨1,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : x = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_2 (t h x : Nat) (f : Registers) :
    step sites (configAt base 2 ⟨t,h,x,f⟩) = configAt base 0 ⟨t,h,x,f⟩ := by
  change step sites ⟨.at (base+2),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+2) = some (expected base 2) := hbound ⟨2,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_3 (t h x : Nat) (f : Registers) :
    step sites (configAt base 3 ⟨t,h,x,f⟩) = configAt base 5 ⟨t,h,x,f⟩ := by
  change step sites ⟨.at (base+3),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+3) = some (expected base 3) := hbound ⟨3,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_4 (t h x : Nat) (f : Registers) :
    step sites (configAt base 4 ⟨t,h,x,f⟩) = if x = 0 then configAt base 10 ⟨t,h,x,f⟩ else configAt base 5 ⟨t,h,x-1,f⟩ := by
  change step sites ⟨.at (base+4),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+4) = some (expected base 4) := hbound ⟨4,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : x = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_5 (t h x : Nat) (f : Registers) :
    step sites (configAt base 5 ⟨t,h,x,f⟩) = if h = 0 then configAt base 7 ⟨t,h,x,f⟩ else configAt base 6 ⟨t,h-1,x,f⟩ := by
  change step sites ⟨.at (base+5),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+5) = some (expected base 5) := hbound ⟨5,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : h = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_6 (t h x : Nat) (f : Registers) :
    step sites (configAt base 6 ⟨t,h,x,f⟩) = configAt base 5 ⟨t,h,x,f⟩ := by
  change step sites ⟨.at (base+6),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+6) = some (expected base 6) := hbound ⟨6,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_7 (t h x : Nat) (f : Registers) :
    step sites (configAt base 7 ⟨t,h,x,f⟩) = if x = 0 then configAt base 9 ⟨t,h,x,f⟩ else configAt base 8 ⟨t,h,x-1,f⟩ := by
  change step sites ⟨.at (base+7),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+7) = some (expected base 7) := hbound ⟨7,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : x = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_8 (t h x : Nat) (f : Registers) :
    step sites (configAt base 8 ⟨t,h,x,f⟩) = configAt base 5 ⟨t,h,x,f⟩ := by
  change step sites ⟨.at (base+8),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+8) = some (expected base 8) := hbound ⟨8,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_9 (t h x : Nat) (f : Registers) :
    step sites (configAt base 9 ⟨t,h,x,f⟩) = configAt base 12 ⟨t,h,x,f⟩ := by
  change step sites ⟨.at (base+9),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+9) = some (expected base 9) := hbound ⟨9,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_10 (t h x : Nat) (f : Registers) :
    step sites (configAt base 10 ⟨t,h,x,f⟩) = if t = 0 then configAt base 12 ⟨t,h,x,f⟩ else configAt base 11 ⟨t-1,h,x,f⟩ := by
  change step sites ⟨.at (base+10),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+10) = some (expected base 10) := hbound ⟨10,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : t = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
theorem step_11 (t h x : Nat) (f : Registers) :
    step sites (configAt base 11 ⟨t,h,x,f⟩) = configAt base 10 ⟨t,h,x,f⟩ := by
  change step sites ⟨.at (base+11),registers ⟨t,h,x,f⟩⟩ = _
  have hb : resolveAt sites (base+11) = some (expected base 11) := hbound ⟨11,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_h,write_x,registers]
end M6.Source.AXGateCompare

