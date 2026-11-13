module
public import M6.Source.AXPushSteps
@[expose] public section
set_option linter.unusedSimpArgs false
namespace M6.Source.AXTimes4
abbrev Store := AXPush.Store
abbrev registers := AXPush.registers
def configAt (base pc : Nat) (s : Store) : Configuration :=
  ⟨.at (base+pc),registers s⟩
def expected (base : Nat) : Nat → Instruction
  | 0 => .dec 7 (some (base+6)) (some (base+1))
  | 1 => .inc 1 (some (base+2))
  | 2 => .inc 1 (some (base+3))
  | 3 => .inc 1 (some (base+4))
  | 4 => .inc 1 (some (base+5))
  | _ => .jump (some base)
def Bound (sites : Array Site) (base : Nat) : Prop :=
  ∀ j : Fin 6, resolveAt sites (base+j.val) = some (expected base j.val)
variable {sites : Array Site} {base : Nat} (hbound : Bound sites base)
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
theorem step_0 (t w x y : Nat) (f : Registers) :
    step sites (configAt base 0 ⟨t,w,x,y,f⟩) = if y = 0 then configAt base 6 ⟨t,w,x,y,f⟩ else configAt base 1 ⟨t,w,x,y-1,f⟩ := by
  change step sites ⟨.at (base+0),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+0) = some (expected base 0) := hbound ⟨0,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : y = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]
theorem step_1 (t w x y : Nat) (f : Registers) :
    step sites (configAt base 1 ⟨t,w,x,y,f⟩) = configAt base 2 ⟨t+1,w,x,y,f⟩ := by
  change step sites ⟨.at (base+1),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+1) = some (expected base 1) := hbound ⟨1,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]
theorem step_2 (t w x y : Nat) (f : Registers) :
    step sites (configAt base 2 ⟨t,w,x,y,f⟩) = configAt base 3 ⟨t+1,w,x,y,f⟩ := by
  change step sites ⟨.at (base+2),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+2) = some (expected base 2) := hbound ⟨2,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]
theorem step_3 (t w x y : Nat) (f : Registers) :
    step sites (configAt base 3 ⟨t,w,x,y,f⟩) = configAt base 4 ⟨t+1,w,x,y,f⟩ := by
  change step sites ⟨.at (base+3),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+3) = some (expected base 3) := hbound ⟨3,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]
theorem step_4 (t w x y : Nat) (f : Registers) :
    step sites (configAt base 4 ⟨t,w,x,y,f⟩) = configAt base 5 ⟨t+1,w,x,y,f⟩ := by
  change step sites ⟨.at (base+4),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+4) = some (expected base 4) := hbound ⟨4,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]
theorem step_5 (t w x y : Nat) (f : Registers) :
    step sites (configAt base 5 ⟨t,w,x,y,f⟩) = configAt base 0 ⟨t,w,x,y,f⟩ := by
  change step sites ⟨.at (base+5),registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt sites (base+5) = some (expected base 5) := hbound ⟨5,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers,AXPush.registers]
theorem times4 (t w x y : Nat) (f : Registers) :
    Steps sites (6*y+1) (configAt base 0 ⟨t,w,x,y,f⟩)
      (configAt base 6 ⟨t+4*y,w,x,0,f⟩) := by
  induction y generalizing t with
  | zero =>
    apply Steps.cons
    rw [step_0 hbound]
    simp only [↓reduceIte,Nat.mul_zero,Nat.add_zero]
    exact Steps.refl _
  | succ y ih =>
    have he : 6*(y+1)+1 = (6*y+1)+1+1+1+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_0 hbound]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_1 hbound]
    apply Steps.cons
    rw [step_2 hbound]
    apply Steps.cons
    rw [step_3 hbound]
    apply Steps.cons
    rw [step_4 hbound]
    apply Steps.cons
    rw [step_5 hbound]
    have ht : t+4*(y+1) = (t+1+1+1+1)+4*y := by omega
    rw [ht]
    exact ih (t+1+1+1+1)
#print axioms times4
end M6.Source.AXTimes4

