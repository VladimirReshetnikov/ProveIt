module
public import M6.Source.AXPushBinding
@[expose] public section
set_option linter.unusedSimpArgs false
namespace M6.Source.AXPush

structure Store where
  t : Nat
  w : Nat
  x : Nat
  y : Nat
  frame : Registers

def registers (s : Store) : Registers := fun r =>
  if r = 1 then s.t else if r = 2 then s.w else if r = 6 then s.x
  else if r = 7 then s.y else s.frame r

def configAt (pc : Nat) (s : Store) : Configuration := ⟨.at pc,registers s⟩
private theorem write_t (s : Store) (v : Nat) :
    write (registers s) 1 v = registers {s with t := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
private theorem write_w (s : Store) (v : Nat) :
    write (registers s) 2 v = registers {s with w := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
private theorem write_x (s : Store) (v : Nat) :
    write (registers s) 6 v = registers {s with x := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
private theorem write_y (s : Store) (v : Nat) :
    write (registers s) 7 v = registers {s with y := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
theorem step_25 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 25 ⟨t,w,x,y,f⟩) = if t = 0 then configAt 28 ⟨t,w,x,y,f⟩ else configAt 26 ⟨t-1,w,x,y,f⟩ := by
  change step exactSites ⟨.at 25,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 25 = some (expected 0) := literal_binding ⟨0,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : t = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_26 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 26 ⟨t,w,x,y,f⟩) = configAt 27 ⟨t,w,x+1,y,f⟩ := by
  change step exactSites ⟨.at 26,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 26 = some (expected 1) := literal_binding ⟨1,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_27 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 27 ⟨t,w,x,y,f⟩) = configAt 25 ⟨t,w,x,y,f⟩ := by
  change step exactSites ⟨.at 27,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 27 = some (expected 2) := literal_binding ⟨2,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_28 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 28 ⟨t,w,x,y,f⟩) = if w = 0 then configAt 31 ⟨t,w,x,y,f⟩ else configAt 29 ⟨t,w-1,x,y,f⟩ := by
  change step exactSites ⟨.at 28,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 28 = some (expected 3) := literal_binding ⟨3,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : w = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_29 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 29 ⟨t,w,x,y,f⟩) = configAt 30 ⟨t+1,w,x,y,f⟩ := by
  change step exactSites ⟨.at 29,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 29 = some (expected 4) := literal_binding ⟨4,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_30 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 30 ⟨t,w,x,y,f⟩) = configAt 28 ⟨t,w,x,y,f⟩ := by
  change step exactSites ⟨.at 30,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 30 = some (expected 5) := literal_binding ⟨5,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_31 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 31 ⟨t,w,x,y,f⟩) = if t = 0 then configAt 35 ⟨t,w,x,y,f⟩ else configAt 32 ⟨t-1,w,x,y,f⟩ := by
  change step exactSites ⟨.at 31,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 31 = some (expected 6) := literal_binding ⟨6,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : t = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_32 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 32 ⟨t,w,x,y,f⟩) = configAt 33 ⟨t,w,x,y+1,f⟩ := by
  change step exactSites ⟨.at 32,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 32 = some (expected 7) := literal_binding ⟨7,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_33 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 33 ⟨t,w,x,y,f⟩) = configAt 34 ⟨t,w,x+1,y,f⟩ := by
  change step exactSites ⟨.at 33,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 33 = some (expected 8) := literal_binding ⟨8,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_34 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 34 ⟨t,w,x,y,f⟩) = configAt 31 ⟨t,w,x,y,f⟩ := by
  change step exactSites ⟨.at 34,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 34 = some (expected 9) := literal_binding ⟨9,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_35 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 35 ⟨t,w,x,y,f⟩) = if x = 0 then configAt 41 ⟨t,w,x,y,f⟩ else configAt 36 ⟨t,w,x-1,y,f⟩ := by
  change step exactSites ⟨.at 35,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 35 = some (expected 10) := literal_binding ⟨10,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : x = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_36 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 36 ⟨t,w,x,y,f⟩) = configAt 37 ⟨t,w,x,y+1,f⟩ := by
  change step exactSites ⟨.at 36,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 36 = some (expected 11) := literal_binding ⟨11,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_37 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 37 ⟨t,w,x,y,f⟩) = if x = 0 then configAt 40 ⟨t,w,x,y,f⟩ else configAt 38 ⟨t,w,x-1,y,f⟩ := by
  change step exactSites ⟨.at 37,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 37 = some (expected 12) := literal_binding ⟨12,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : x = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_38 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 38 ⟨t,w,x,y,f⟩) = configAt 39 ⟨t+1,w,x,y,f⟩ := by
  change step exactSites ⟨.at 38,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 38 = some (expected 13) := literal_binding ⟨13,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_39 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 39 ⟨t,w,x,y,f⟩) = configAt 37 ⟨t,w,x,y,f⟩ := by
  change step exactSites ⟨.at 39,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 39 = some (expected 14) := literal_binding ⟨14,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_40 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 40 ⟨t,w,x,y,f⟩) = configAt 31 ⟨t,w,x,y,f⟩ := by
  change step exactSites ⟨.at 40,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 40 = some (expected 15) := literal_binding ⟨15,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_41 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 41 ⟨t,w,x,y,f⟩) = if y = 0 then configAt 44 ⟨t,w,x,y,f⟩ else configAt 42 ⟨t,w,x,y-1,f⟩ := by
  change step exactSites ⟨.at 41,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 41 = some (expected 16) := literal_binding ⟨16,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : y = 0
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_42 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 42 ⟨t,w,x,y,f⟩) = configAt 43 ⟨t,w+1,x,y,f⟩ := by
  change step exactSites ⟨.at 42,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 42 = some (expected 17) := literal_binding ⟨17,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

theorem step_43 (t w x y : Nat) (f : Registers) :
    step exactSites (configAt 43 ⟨t,w,x,y,f⟩) = configAt 41 ⟨t,w,x,y,f⟩ := by
  change step exactSites ⟨.at 43,registers ⟨t,w,x,y,f⟩⟩ = _
  have hb : resolveAt exactSites 43 = some (expected 18) := literal_binding ⟨18,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [expected,execute,destination,configAt,write_t,write_w,write_x,write_y,registers]

end M6.Source.AXPush

