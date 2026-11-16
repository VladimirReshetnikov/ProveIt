module
public import M6.Source.Determinism
public import PA196.Program
/-! Arithmetic proof adapted from M6.Source.MPGuardSteps; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace PA196.Source.MPGuard
open M6.Source

def registers (t h x : Nat) (f : Registers) : Registers := fun r =>
  if r = 1 then t else if r = 5 then h else if r = 6 then x else f r

def config (pc t h x : Nat) (f : Registers) : Configuration :=
  ⟨.at pc,registers t h x f⟩
private theorem write_t (t h x z : Nat) (f : Registers) :
    write (registers t h x f) 1 z = registers z h x f := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;>
    simp_all [registers,write]
private theorem write_h (t h x z : Nat) (f : Registers) :
    write (registers t h x f) 5 z = registers t z x f := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;>
    simp_all [registers,write]
private theorem write_x (t h x z : Nat) (f : Registers) :
    write (registers t h x f) 6 z = registers t h z f := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;>
    simp_all [registers,write]
private theorem row3760 : resolveAt Program.sites 3760 = some (.dec 1 (some 3763) (some 3761)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3760 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3760 t h x f) = if t = 0 then config 3763 t h x f else config 3761 (t-1) h x f := by
  rw [config,step_of_resolved row3760]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3761 : resolveAt Program.sites 3761 = some (.inc 6 (some 3762)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3761 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3761 t h x f) = config 3762 t h (x+1) f := by
  rw [config,step_of_resolved row3761]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3762 : resolveAt Program.sites 3762 = some (.jump (some 3760)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3762 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3762 t h x f) = config 3760 t h x f := by
  rw [config,step_of_resolved row3762]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3763 : resolveAt Program.sites 3763 = some (.dec 5 (some 3767) (some 3764)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3763 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3763 t h x f) = if h = 0 then config 3767 t h x f else config 3764 t (h-1) x f := by
  rw [config,step_of_resolved row3763]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3764 : resolveAt Program.sites 3764 = some (.dec 6 (some 3766) (some 3765)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3764 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3764 t h x f) = if x = 0 then config 3766 t h x f else config 3765 t h (x-1) f := by
  rw [config,step_of_resolved row3764]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3765 : resolveAt Program.sites 3765 = some (.jump (some 3763)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3765 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3765 t h x f) = config 3763 t h x f := by
  rw [config,step_of_resolved row3765]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3766 : resolveAt Program.sites 3766 = some (.jump (some 3768)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3766 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3766 t h x f) = config 3768 t h x f := by
  rw [config,step_of_resolved row3766]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3767 : resolveAt Program.sites 3767 = some (.dec 6 (some 3773) (some 3768)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3767 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3767 t h x f) = if x = 0 then config 3773 t h x f else config 3768 t h (x-1) f := by
  rw [config,step_of_resolved row3767]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3768 : resolveAt Program.sites 3768 = some (.dec 5 (some 3770) (some 3769)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3768 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3768 t h x f) = if h = 0 then config 3770 t h x f else config 3769 t (h-1) x f := by
  rw [config,step_of_resolved row3768]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3769 : resolveAt Program.sites 3769 = some (.jump (some 3768)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3769 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3769 t h x f) = config 3768 t h x f := by
  rw [config,step_of_resolved row3769]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3770 : resolveAt Program.sites 3770 = some (.dec 6 (some 3772) (some 3771)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3770 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3770 t h x f) = if x = 0 then config 3772 t h x f else config 3771 t h (x-1) f := by
  rw [config,step_of_resolved row3770]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3771 : resolveAt Program.sites 3771 = some (.jump (some 3768)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3771 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3771 t h x f) = config 3768 t h x f := by
  rw [config,step_of_resolved row3771]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3772 : resolveAt Program.sites 3772 = some (.jump (some 3799)) := by
  rw [Program.resolve_tree]
  rfl
theorem step3772 (t h x : Nat) (f : Registers) :
    step Program.sites (config 3772 t h x f) = config 3799 t h x f := by
  rw [config,step_of_resolved row3772]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
end PA196.Source.MPGuard

