module
public import M6.Source.Determinism
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace M6.Source.MPGuard

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
private theorem row3871 : resolveAt exactSites 3871 = some (.dec 1 (some 3874) (some 3872)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3871 (t h x : Nat) (f : Registers) :
    step exactSites (config 3871 t h x f) = if t = 0 then config 3874 t h x f else config 3872 (t-1) h x f := by
  rw [config,step_of_resolved row3871]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3872 : resolveAt exactSites 3872 = some (.inc 6 (some 3873)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3872 (t h x : Nat) (f : Registers) :
    step exactSites (config 3872 t h x f) = config 3873 t h (x+1) f := by
  rw [config,step_of_resolved row3872]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3873 : resolveAt exactSites 3873 = some (.jump (some 3871)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3873 (t h x : Nat) (f : Registers) :
    step exactSites (config 3873 t h x f) = config 3871 t h x f := by
  rw [config,step_of_resolved row3873]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3874 : resolveAt exactSites 3874 = some (.dec 5 (some 3878) (some 3875)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3874 (t h x : Nat) (f : Registers) :
    step exactSites (config 3874 t h x f) = if h = 0 then config 3878 t h x f else config 3875 t (h-1) x f := by
  rw [config,step_of_resolved row3874]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3875 : resolveAt exactSites 3875 = some (.dec 6 (some 3877) (some 3876)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3875 (t h x : Nat) (f : Registers) :
    step exactSites (config 3875 t h x f) = if x = 0 then config 3877 t h x f else config 3876 t h (x-1) f := by
  rw [config,step_of_resolved row3875]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3876 : resolveAt exactSites 3876 = some (.jump (some 3874)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3876 (t h x : Nat) (f : Registers) :
    step exactSites (config 3876 t h x f) = config 3874 t h x f := by
  rw [config,step_of_resolved row3876]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3877 : resolveAt exactSites 3877 = some (.jump (some 3879)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3877 (t h x : Nat) (f : Registers) :
    step exactSites (config 3877 t h x f) = config 3879 t h x f := by
  rw [config,step_of_resolved row3877]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3878 : resolveAt exactSites 3878 = some (.dec 6 (some 3884) (some 3879)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3878 (t h x : Nat) (f : Registers) :
    step exactSites (config 3878 t h x f) = if x = 0 then config 3884 t h x f else config 3879 t h (x-1) f := by
  rw [config,step_of_resolved row3878]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3879 : resolveAt exactSites 3879 = some (.dec 5 (some 3881) (some 3880)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3879 (t h x : Nat) (f : Registers) :
    step exactSites (config 3879 t h x f) = if h = 0 then config 3881 t h x f else config 3880 t (h-1) x f := by
  rw [config,step_of_resolved row3879]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3880 : resolveAt exactSites 3880 = some (.jump (some 3879)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3880 (t h x : Nat) (f : Registers) :
    step exactSites (config 3880 t h x f) = config 3879 t h x f := by
  rw [config,step_of_resolved row3880]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3881 : resolveAt exactSites 3881 = some (.dec 6 (some 3883) (some 3882)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3881 (t h x : Nat) (f : Registers) :
    step exactSites (config 3881 t h x f) = if x = 0 then config 3883 t h x f else config 3882 t h (x-1) f := by
  rw [config,step_of_resolved row3881]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3882 : resolveAt exactSites 3882 = some (.jump (some 3879)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3882 (t h x : Nat) (f : Registers) :
    step exactSites (config 3882 t h x f) = config 3879 t h x f := by
  rw [config,step_of_resolved row3882]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
private theorem row3883 : resolveAt exactSites 3883 = some (.jump (some 3910)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step3883 (t h x : Nat) (f : Registers) :
    step exactSites (config 3883 t h x f) = config 3910 t h x f := by
  rw [config,step_of_resolved row3883]
  simp [execute,destination,config,write_t,write_h,write_x,registers]
end M6.Source.MPGuard

