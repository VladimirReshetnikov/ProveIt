module
public import PA196.Source.AXGateBinding
/-! Arithmetic proof adapted from the corresponding M6 module.
All source-row bindings below refer to the PA196 tree. -/
@[expose] public section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace PA196.Source.AXGate
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
private theorem row3658 : resolveAt Program.sites 3658 = some (.dec 3 (some 3662) (some 3659)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3658 (s : Store) : step Program.sites (configAt 3658 s) = if s.a=0 then configAt 3662 s else configAt 3659 {s with a := s.a-1} := by
  change step Program.sites ⟨.at 3658,registers s⟩ = _
  rw [step_of_resolved row3658]
  by_cases hz : s.a = 0
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3659 : resolveAt Program.sites 3659 = some (.inc 7 (some 3660)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3659 (s : Store) : step Program.sites (configAt 3659 s) = configAt 3660 {s with y := s.y+1} := by
  change step Program.sites ⟨.at 3659,registers s⟩ = _
  rw [step_of_resolved row3659]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3660 : resolveAt Program.sites 3660 = some (.inc 6 (some 3661)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3660 (s : Store) : step Program.sites (configAt 3660 s) = configAt 3661 {s with x := s.x+1} := by
  change step Program.sites ⟨.at 3660,registers s⟩ = _
  rw [step_of_resolved row3660]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3661 : resolveAt Program.sites 3661 = some (.jump (some 3658)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3661 (s : Store) : step Program.sites (configAt 3661 s) = configAt 3658 s := by
  change step Program.sites ⟨.at 3661,registers s⟩ = _
  rw [step_of_resolved row3661]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3674 : resolveAt Program.sites 3674 = some (.dec 7 (some 3677) (some 3675)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3674 (s : Store) : step Program.sites (configAt 3674 s) = if s.y=0 then configAt 3677 s else configAt 3675 {s with y := s.y-1} := by
  change step Program.sites ⟨.at 3674,registers s⟩ = _
  rw [step_of_resolved row3674]
  by_cases hz : s.y = 0
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3675 : resolveAt Program.sites 3675 = some (.inc 6 (some 3676)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3675 (s : Store) : step Program.sites (configAt 3675 s) = configAt 3676 {s with x := s.x+1} := by
  change step Program.sites ⟨.at 3675,registers s⟩ = _
  rw [step_of_resolved row3675]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3676 : resolveAt Program.sites 3676 = some (.jump (some 3674)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3676 (s : Store) : step Program.sites (configAt 3676 s) = configAt 3674 s := by
  change step Program.sites ⟨.at 3676,registers s⟩ = _
  rw [step_of_resolved row3676]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3677 : resolveAt Program.sites 3677 = some (.dec 4 (some 3680) (some 3678)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3677 (s : Store) : step Program.sites (configAt 3677 s) = if s.d=0 then configAt 3680 s else configAt 3678 {s with d := s.d-1} := by
  change step Program.sites ⟨.at 3677,registers s⟩ = _
  rw [step_of_resolved row3677]
  by_cases hz : s.d = 0
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3678 : resolveAt Program.sites 3678 = some (.inc 5 (some 3679)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3678 (s : Store) : step Program.sites (configAt 3678 s) = configAt 3679 {s with h := s.h+1} := by
  change step Program.sites ⟨.at 3678,registers s⟩ = _
  rw [step_of_resolved row3678]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3679 : resolveAt Program.sites 3679 = some (.jump (some 3677)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3679 (s : Store) : step Program.sites (configAt 3679 s) = configAt 3677 s := by
  change step Program.sites ⟨.at 3679,registers s⟩ = _
  rw [step_of_resolved row3679]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3692 : resolveAt Program.sites 3692 = some (.jump (some 3799)) := by
  rw [Program.resolve_tree]
  rfl
theorem step_3692 (s : Store) : step Program.sites (configAt 3692 s) = configAt 3799 s := by
  change step Program.sites ⟨.at 3692,registers s⟩ = _
  rw [step_of_resolved row3692]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
end PA196.Source.AXGate

