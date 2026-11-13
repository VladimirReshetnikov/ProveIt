module
public import M6.Source.Unpair
@[expose] public section
set_option linter.unusedSimpArgs false
namespace M6.Source.UnpairPartial
abbrev Store := Unpair.Store
abbrev registers := Unpair.registers

def configAt (base pc : Nat) (s : Store) : Configuration :=
  ⟨.at (base+(pc-3933)),registers s⟩

def expected (base : Nat) : Nat → Instruction
  | 0 => .dec 2 (some (base+8)) (some (base+1))
  | 1 => .inc 7 (some (base+2))
  | 2 => .dec 6 (some (base+4)) (some (base+3))
  | 3 => .jump (some (base+7))
  | 4 => .dec 7 (some (base+7)) (some (base+5))
  | 5 => .inc 6 (some (base+6))
  | 6 => .jump (some (base+4))
  | 7 => .jump (some (base+0))
  | 8 => .dec 7 (some (base+11)) (some (base+9))
  | 9 => .inc 2 (some (base+10))
  | 10 => .jump (some (base+8))
  | _ => .jump (some (base+11))

def Bound (sites : Array Site) (base : Nat) : Prop :=
  ∀ j : Fin 11, resolveAt sites (base+j.val) = some (expected base j.val)

variable {sites : Array Site} {base : Nat} (hbound : Bound sites base)
private theorem write_w (s : Store) (v : Nat) :
    write (registers s) 2 v = registers {s with w := v} := by
  funext r
  by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers,Unpair.registers]
private theorem write_h (s : Store) (v : Nat) :
    write (registers s) 5 v = registers {s with h := v} := by
  funext r
  by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers,Unpair.registers]
private theorem write_x (s : Store) (v : Nat) :
    write (registers s) 6 v = registers {s with x := v} := by
  funext r
  by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers,Unpair.registers]
private theorem write_y (s : Store) (v : Nat) :
    write (registers s) 7 v = registers {s with y := v} := by
  funext r
  by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers,Unpair.registers]

include hbound

theorem step_3933 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3933 ⟨w,h,x,y,f⟩) = if w = 0 then configAt base 3941 ⟨w,h,x,y,f⟩ else configAt base 3934 ⟨w-1,h,x,y,f⟩ := by
  change step sites ⟨.at (base+0),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+0) = some (expected base 0) := hbound ⟨0,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : w = 0
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3934 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3934 ⟨w,h,x,y,f⟩) = configAt base 3935 ⟨w,h,x,y+1,f⟩ := by
  change step sites ⟨.at (base+1),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+1) = some (expected base 1) := hbound ⟨1,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3935 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3935 ⟨w,h,x,y,f⟩) = if x = 0 then configAt base 3937 ⟨w,h,x,y,f⟩ else configAt base 3936 ⟨w,h,x-1,y,f⟩ := by
  change step sites ⟨.at (base+2),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+2) = some (expected base 2) := hbound ⟨2,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : x = 0
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3936 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3936 ⟨w,h,x,y,f⟩) = configAt base 3940 ⟨w,h,x,y,f⟩ := by
  change step sites ⟨.at (base+3),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+3) = some (expected base 3) := hbound ⟨3,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3937 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3937 ⟨w,h,x,y,f⟩) = if y = 0 then configAt base 3940 ⟨w,h,x,y,f⟩ else configAt base 3938 ⟨w,h,x,y-1,f⟩ := by
  change step sites ⟨.at (base+4),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+4) = some (expected base 4) := hbound ⟨4,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : y = 0
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3938 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3938 ⟨w,h,x,y,f⟩) = configAt base 3939 ⟨w,h,x+1,y,f⟩ := by
  change step sites ⟨.at (base+5),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+5) = some (expected base 5) := hbound ⟨5,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3939 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3939 ⟨w,h,x,y,f⟩) = configAt base 3937 ⟨w,h,x,y,f⟩ := by
  change step sites ⟨.at (base+6),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+6) = some (expected base 6) := hbound ⟨6,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3940 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3940 ⟨w,h,x,y,f⟩) = configAt base 3933 ⟨w,h,x,y,f⟩ := by
  change step sites ⟨.at (base+7),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+7) = some (expected base 7) := hbound ⟨7,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3941 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3941 ⟨w,h,x,y,f⟩) = if y = 0 then configAt base 3944 ⟨w,h,x,y,f⟩ else configAt base 3942 ⟨w,h,x,y-1,f⟩ := by
  change step sites ⟨.at (base+8),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+8) = some (expected base 8) := hbound ⟨8,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : y = 0
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3942 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3942 ⟨w,h,x,y,f⟩) = configAt base 3943 ⟨w+1,h,x,y,f⟩ := by
  change step sites ⟨.at (base+9),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+9) = some (expected base 9) := hbound ⟨9,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

theorem step_3943 (w h x y : Nat) (f : Registers) :
    step sites (configAt base 3943 ⟨w,h,x,y,f⟩) = configAt base 3941 ⟨w,h,x,y,f⟩ := by
  change step sites ⟨.at (base+10),registers ⟨w,h,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+10) = some (expected base 10) := hbound ⟨10,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_w,write_h,write_x,write_y,registers,Unpair.registers]

end M6.Source.UnpairPartial

