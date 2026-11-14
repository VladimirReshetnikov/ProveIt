import PA194AXGateBinding
/-! Arithmetic proof adapted from the corresponding M6 module.
The row bindings are rechecked against the PA194 tree. -/
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace PA194AXGate
open M6.Source
structure Store where
  t : Nat
  a : Nat
  d : Nat
  h : Nat
  x : Nat
  y : Nat
  frame : Registers
def registers (s : Store) : Registers := fun r =>
  if r = 1 then s.t else if r = 3 then s.a else if r = 4 then s.d else if r = 5 then s.h else if r = 6 then s.x else if r = 7 then s.y else s.frame r
def configAt (pc : Nat) (s : Store) : Configuration := ⟨.at pc,registers s⟩
private theorem write_t (s : Store) (v : Nat) :
    write (registers s) 1 v = registers {s with t := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
private theorem write_a (s : Store) (v : Nat) :
    write (registers s) 3 v = registers {s with a := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
private theorem write_d (s : Store) (v : Nat) :
    write (registers s) 4 v = registers {s with d := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
private theorem write_h (s : Store) (v : Nat) :
    write (registers s) 5 v = registers {s with h := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
private theorem write_x (s : Store) (v : Nat) :
    write (registers s) 6 v = registers {s with x := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
private theorem write_y (s : Store) (v : Nat) :
    write (registers s) 7 v = registers {s with y := v} := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write,registers]
private theorem row3519 : resolveAt PA194SourceProgram.sites 3519 = some (.dec 3 (some 3523) (some 3520)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3519 (s : Store) : step PA194SourceProgram.sites (configAt 3519 s) = if s.a=0 then configAt 3523 s else configAt 3520 {s with a := s.a-1} := by
  change step PA194SourceProgram.sites ⟨.at 3519,registers s⟩ = _
  rw [step_of_resolved row3519]
  by_cases hz : s.a = 0
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3520 : resolveAt PA194SourceProgram.sites 3520 = some (.inc 7 (some 3521)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3520 (s : Store) : step PA194SourceProgram.sites (configAt 3520 s) = configAt 3521 {s with y := s.y+1} := by
  change step PA194SourceProgram.sites ⟨.at 3520,registers s⟩ = _
  rw [step_of_resolved row3520]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3521 : resolveAt PA194SourceProgram.sites 3521 = some (.inc 6 (some 3522)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3521 (s : Store) : step PA194SourceProgram.sites (configAt 3521 s) = configAt 3522 {s with x := s.x+1} := by
  change step PA194SourceProgram.sites ⟨.at 3521,registers s⟩ = _
  rw [step_of_resolved row3521]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3522 : resolveAt PA194SourceProgram.sites 3522 = some (.jump (some 3519)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3522 (s : Store) : step PA194SourceProgram.sites (configAt 3522 s) = configAt 3519 s := by
  change step PA194SourceProgram.sites ⟨.at 3522,registers s⟩ = _
  rw [step_of_resolved row3522]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3535 : resolveAt PA194SourceProgram.sites 3535 = some (.dec 7 (some 3538) (some 3536)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3535 (s : Store) : step PA194SourceProgram.sites (configAt 3535 s) = if s.y=0 then configAt 3538 s else configAt 3536 {s with y := s.y-1} := by
  change step PA194SourceProgram.sites ⟨.at 3535,registers s⟩ = _
  rw [step_of_resolved row3535]
  by_cases hz : s.y = 0
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3536 : resolveAt PA194SourceProgram.sites 3536 = some (.inc 6 (some 3537)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3536 (s : Store) : step PA194SourceProgram.sites (configAt 3536 s) = configAt 3537 {s with x := s.x+1} := by
  change step PA194SourceProgram.sites ⟨.at 3536,registers s⟩ = _
  rw [step_of_resolved row3536]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3537 : resolveAt PA194SourceProgram.sites 3537 = some (.jump (some 3535)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3537 (s : Store) : step PA194SourceProgram.sites (configAt 3537 s) = configAt 3535 s := by
  change step PA194SourceProgram.sites ⟨.at 3537,registers s⟩ = _
  rw [step_of_resolved row3537]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3538 : resolveAt PA194SourceProgram.sites 3538 = some (.dec 4 (some 3541) (some 3539)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3538 (s : Store) : step PA194SourceProgram.sites (configAt 3538 s) = if s.d=0 then configAt 3541 s else configAt 3539 {s with d := s.d-1} := by
  change step PA194SourceProgram.sites ⟨.at 3538,registers s⟩ = _
  rw [step_of_resolved row3538]
  by_cases hz : s.d = 0
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3539 : resolveAt PA194SourceProgram.sites 3539 = some (.inc 5 (some 3540)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3539 (s : Store) : step PA194SourceProgram.sites (configAt 3539 s) = configAt 3540 {s with h := s.h+1} := by
  change step PA194SourceProgram.sites ⟨.at 3539,registers s⟩ = _
  rw [step_of_resolved row3539]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3540 : resolveAt PA194SourceProgram.sites 3540 = some (.jump (some 3538)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3540 (s : Store) : step PA194SourceProgram.sites (configAt 3540 s) = configAt 3538 s := by
  change step PA194SourceProgram.sites ⟨.at 3540,registers s⟩ = _
  rw [step_of_resolved row3540]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3553 : resolveAt PA194SourceProgram.sites 3553 = some (.jump (some 3660)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step_3553 (s : Store) : step PA194SourceProgram.sites (configAt 3553 s) = configAt 3660 s := by
  change step PA194SourceProgram.sites ⟨.at 3553,registers s⟩ = _
  rw [step_of_resolved row3553]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
end PA194AXGate

