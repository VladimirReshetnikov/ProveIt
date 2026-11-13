module
public import M6.Source.AXPushSteps
@[expose] public section
set_option linter.unusedSimpArgs false
namespace M6.Source.AXPushParam
abbrev Store := AXPush.Store
abbrev registers := AXPush.registers
abbrev expected := AXPush.expected

def configAt (offset pc : Nat) (s : Store) : Configuration :=
  ⟨.at (offset+pc),registers s⟩

def relocate (offset : Nat) : Instruction → Instruction
  | .inc r n => .inc r (n.map (offset+·))
  | .dec r z n => .dec r (z.map (offset+·)) (n.map (offset+·))
  | .jump n => .jump (n.map (offset+·))
  | .halt => .halt

/-- Concrete source copies must supply all resolved row equalities. -/
def Bound (sites : Array Site) (offset : Nat) : Prop :=
  ∀ j : Fin 19, resolveAt sites (offset+(25+j.val)) =
    some (relocate offset (expected j.val))

variable {sites : Array Site} {offset : Nat} (hbound : Bound sites offset)

private theorem write_t (s : Store) (v : Nat) :
    write (registers s) 1 v = registers {s with t := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers,AXPush.registers]
private theorem write_w (s : Store) (v : Nat) :
    write (registers s) 2 v = registers {s with w := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers,AXPush.registers]
private theorem write_x (s : Store) (v : Nat) :
    write (registers s) 6 v = registers {s with x := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers,AXPush.registers]
private theorem write_y (s : Store) (v : Nat) :
    write (registers s) 7 v = registers {s with y := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers,AXPush.registers]
include hbound

theorem step_25 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 25 ⟨t,w,x,y,f⟩) = if t = 0 then configAt offset 28 ⟨t,w,x,y,f⟩ else configAt offset 26 ⟨t-1,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+25),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+25) = some (relocate offset (expected 0)) := hbound ⟨0,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : t = 0
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_26 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 26 ⟨t,w,x,y,f⟩) = configAt offset 27 ⟨t,w,x+1,y,f⟩ := by
  change step sites ⟨.at (offset+26),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+26) = some (relocate offset (expected 1)) := hbound ⟨1,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_27 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 27 ⟨t,w,x,y,f⟩) = configAt offset 25 ⟨t,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+27),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+27) = some (relocate offset (expected 2)) := hbound ⟨2,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_28 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 28 ⟨t,w,x,y,f⟩) = if w = 0 then configAt offset 31 ⟨t,w,x,y,f⟩ else configAt offset 29 ⟨t,w-1,x,y,f⟩ := by
  change step sites ⟨.at (offset+28),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+28) = some (relocate offset (expected 3)) := hbound ⟨3,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : w = 0
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_29 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 29 ⟨t,w,x,y,f⟩) = configAt offset 30 ⟨t+1,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+29),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+29) = some (relocate offset (expected 4)) := hbound ⟨4,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_30 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 30 ⟨t,w,x,y,f⟩) = configAt offset 28 ⟨t,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+30),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+30) = some (relocate offset (expected 5)) := hbound ⟨5,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_31 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 31 ⟨t,w,x,y,f⟩) = if t = 0 then configAt offset 35 ⟨t,w,x,y,f⟩ else configAt offset 32 ⟨t-1,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+31),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+31) = some (relocate offset (expected 6)) := hbound ⟨6,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : t = 0
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_32 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 32 ⟨t,w,x,y,f⟩) = configAt offset 33 ⟨t,w,x,y+1,f⟩ := by
  change step sites ⟨.at (offset+32),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+32) = some (relocate offset (expected 7)) := hbound ⟨7,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_33 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 33 ⟨t,w,x,y,f⟩) = configAt offset 34 ⟨t,w,x+1,y,f⟩ := by
  change step sites ⟨.at (offset+33),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+33) = some (relocate offset (expected 8)) := hbound ⟨8,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_34 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 34 ⟨t,w,x,y,f⟩) = configAt offset 31 ⟨t,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+34),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+34) = some (relocate offset (expected 9)) := hbound ⟨9,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_35 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 35 ⟨t,w,x,y,f⟩) = if x = 0 then configAt offset 41 ⟨t,w,x,y,f⟩ else configAt offset 36 ⟨t,w,x-1,y,f⟩ := by
  change step sites ⟨.at (offset+35),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+35) = some (relocate offset (expected 10)) := hbound ⟨10,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : x = 0
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_36 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 36 ⟨t,w,x,y,f⟩) = configAt offset 37 ⟨t,w,x,y+1,f⟩ := by
  change step sites ⟨.at (offset+36),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+36) = some (relocate offset (expected 11)) := hbound ⟨11,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_37 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 37 ⟨t,w,x,y,f⟩) = if x = 0 then configAt offset 40 ⟨t,w,x,y,f⟩ else configAt offset 38 ⟨t,w,x-1,y,f⟩ := by
  change step sites ⟨.at (offset+37),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+37) = some (relocate offset (expected 12)) := hbound ⟨12,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : x = 0
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_38 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 38 ⟨t,w,x,y,f⟩) = configAt offset 39 ⟨t+1,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+38),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+38) = some (relocate offset (expected 13)) := hbound ⟨13,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_39 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 39 ⟨t,w,x,y,f⟩) = configAt offset 37 ⟨t,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+39),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+39) = some (relocate offset (expected 14)) := hbound ⟨14,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_40 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 40 ⟨t,w,x,y,f⟩) = configAt offset 31 ⟨t,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+40),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+40) = some (relocate offset (expected 15)) := hbound ⟨15,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_41 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 41 ⟨t,w,x,y,f⟩) = if y = 0 then configAt offset 44 ⟨t,w,x,y,f⟩ else configAt offset 42 ⟨t,w,x,y-1,f⟩ := by
  change step sites ⟨.at (offset+41),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+41) = some (relocate offset (expected 16)) := hbound ⟨16,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : y = 0
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_42 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 42 ⟨t,w,x,y,f⟩) = configAt offset 43 ⟨t,w+1,x,y,f⟩ := by
  change step sites ⟨.at (offset+42),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+42) = some (relocate offset (expected 17)) := hbound ⟨17,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

theorem step_43 (t w x y : Nat) (f : Registers) :
    step sites (configAt offset 43 ⟨t,w,x,y,f⟩) = configAt offset 41 ⟨t,w,x,y,f⟩ := by
  change step sites ⟨.at (offset+43),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (offset+43) = some (relocate offset (expected 18)) := hbound ⟨18,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,AXPush.expected,relocate,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]

end M6.Source.AXPushParam

