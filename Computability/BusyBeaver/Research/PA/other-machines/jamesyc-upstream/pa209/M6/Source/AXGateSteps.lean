module
public import M6.Source.AXGateBinding
@[expose] public section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace M6.Source.AXGate
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
private theorem row3769 : resolveAt exactSites 3769 = some (.dec 3 (some 3773) (some 3770)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3769 (s : Store) : step exactSites (configAt 3769 s) = if s.a=0 then configAt 3773 s else configAt 3770 {s with a := s.a-1} := by
  change step exactSites ⟨.at 3769,registers s⟩ = _
  rw [step_of_resolved row3769]
  by_cases hz : s.a = 0
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3770 : resolveAt exactSites 3770 = some (.inc 7 (some 3771)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3770 (s : Store) : step exactSites (configAt 3770 s) = configAt 3771 {s with y := s.y+1} := by
  change step exactSites ⟨.at 3770,registers s⟩ = _
  rw [step_of_resolved row3770]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3771 : resolveAt exactSites 3771 = some (.inc 6 (some 3772)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3771 (s : Store) : step exactSites (configAt 3771 s) = configAt 3772 {s with x := s.x+1} := by
  change step exactSites ⟨.at 3771,registers s⟩ = _
  rw [step_of_resolved row3771]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3772 : resolveAt exactSites 3772 = some (.jump (some 3769)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3772 (s : Store) : step exactSites (configAt 3772 s) = configAt 3769 s := by
  change step exactSites ⟨.at 3772,registers s⟩ = _
  rw [step_of_resolved row3772]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3785 : resolveAt exactSites 3785 = some (.dec 7 (some 3788) (some 3786)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3785 (s : Store) : step exactSites (configAt 3785 s) = if s.y=0 then configAt 3788 s else configAt 3786 {s with y := s.y-1} := by
  change step exactSites ⟨.at 3785,registers s⟩ = _
  rw [step_of_resolved row3785]
  by_cases hz : s.y = 0
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3786 : resolveAt exactSites 3786 = some (.inc 6 (some 3787)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3786 (s : Store) : step exactSites (configAt 3786 s) = configAt 3787 {s with x := s.x+1} := by
  change step exactSites ⟨.at 3786,registers s⟩ = _
  rw [step_of_resolved row3786]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3787 : resolveAt exactSites 3787 = some (.jump (some 3785)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3787 (s : Store) : step exactSites (configAt 3787 s) = configAt 3785 s := by
  change step exactSites ⟨.at 3787,registers s⟩ = _
  rw [step_of_resolved row3787]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3788 : resolveAt exactSites 3788 = some (.dec 4 (some 3791) (some 3789)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3788 (s : Store) : step exactSites (configAt 3788 s) = if s.d=0 then configAt 3791 s else configAt 3789 {s with d := s.d-1} := by
  change step exactSites ⟨.at 3788,registers s⟩ = _
  rw [step_of_resolved row3788]
  by_cases hz : s.d = 0
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3789 : resolveAt exactSites 3789 = some (.inc 5 (some 3790)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3789 (s : Store) : step exactSites (configAt 3789 s) = configAt 3790 {s with h := s.h+1} := by
  change step exactSites ⟨.at 3789,registers s⟩ = _
  rw [step_of_resolved row3789]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3790 : resolveAt exactSites 3790 = some (.jump (some 3788)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3790 (s : Store) : step exactSites (configAt 3790 s) = configAt 3788 s := by
  change step exactSites ⟨.at 3790,registers s⟩ = _
  rw [step_of_resolved row3790]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
private theorem row3803 : resolveAt exactSites 3803 = some (.jump (some 3910)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem step_3803 (s : Store) : step exactSites (configAt 3803 s) = configAt 3910 s := by
  change step exactSites ⟨.at 3803,registers s⟩ = _
  rw [step_of_resolved row3803]
  all_goals simp_all [execute,destination,configAt,write_t,write_a,write_d,write_h,write_x,write_y,registers]
end M6.Source.AXGate

