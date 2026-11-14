import M6.Source.Determinism
import PA194SourceProgram
/-! Arithmetic proof adapted from M6.Source.MPGuardSteps; every literal
source binding is reproved against the PA194 program. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace PA194MPSource.MPGuard
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
private theorem row3621 : resolveAt PA194SourceProgram.sites 3621 = some (.dec 1 (some 3624) (some 3622)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3621 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3621 t h x f) = if t = 0 then config 3624 t h x f else config 3622 (t-1) h x f := by
  rw [config,step_of_resolved row3621]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3622 : resolveAt PA194SourceProgram.sites 3622 = some (.inc 6 (some 3623)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3622 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3622 t h x f) = config 3623 t h (x+1) f := by
  rw [config,step_of_resolved row3622]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3623 : resolveAt PA194SourceProgram.sites 3623 = some (.jump (some 3621)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3623 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3623 t h x f) = config 3621 t h x f := by
  rw [config,step_of_resolved row3623]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3624 : resolveAt PA194SourceProgram.sites 3624 = some (.dec 5 (some 3628) (some 3625)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3624 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3624 t h x f) = if h = 0 then config 3628 t h x f else config 3625 t (h-1) x f := by
  rw [config,step_of_resolved row3624]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3625 : resolveAt PA194SourceProgram.sites 3625 = some (.dec 6 (some 3627) (some 3626)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3625 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3625 t h x f) = if x = 0 then config 3627 t h x f else config 3626 t h (x-1) f := by
  rw [config,step_of_resolved row3625]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3626 : resolveAt PA194SourceProgram.sites 3626 = some (.jump (some 3624)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3626 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3626 t h x f) = config 3624 t h x f := by
  rw [config,step_of_resolved row3626]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3627 : resolveAt PA194SourceProgram.sites 3627 = some (.jump (some 3629)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3627 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3627 t h x f) = config 3629 t h x f := by
  rw [config,step_of_resolved row3627]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3628 : resolveAt PA194SourceProgram.sites 3628 = some (.dec 6 (some 3634) (some 3629)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3628 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3628 t h x f) = if x = 0 then config 3634 t h x f else config 3629 t h (x-1) f := by
  rw [config,step_of_resolved row3628]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3629 : resolveAt PA194SourceProgram.sites 3629 = some (.dec 5 (some 3631) (some 3630)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3629 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3629 t h x f) = if h = 0 then config 3631 t h x f else config 3630 t (h-1) x f := by
  rw [config,step_of_resolved row3629]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3630 : resolveAt PA194SourceProgram.sites 3630 = some (.jump (some 3629)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3630 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3630 t h x f) = config 3629 t h x f := by
  rw [config,step_of_resolved row3630]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3631 : resolveAt PA194SourceProgram.sites 3631 = some (.dec 6 (some 3633) (some 3632)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3631 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3631 t h x f) = if x = 0 then config 3633 t h x f else config 3632 t h (x-1) f := by
  rw [config,step_of_resolved row3631]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3632 : resolveAt PA194SourceProgram.sites 3632 = some (.jump (some 3629)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3632 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3632 t h x f) = config 3629 t h x f := by
  rw [config,step_of_resolved row3632]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3633 : resolveAt PA194SourceProgram.sites 3633 = some (.jump (some 3660)) := by
  rw [PA194SourceProgram.resolve_tree]
  rfl
theorem step3633 (t h x : Nat) (f : Registers) :
    step PA194SourceProgram.sites (config 3633 t h x f) = config 3660 t h x f := by
  rw [config,step_of_resolved row3633]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
end PA194MPSource.MPGuard

