module
public import PA196.Source.FetchPrefixBinding
public import M6.Source.Determinism
/-! Arithmetic proof adapted from M6.Source.FetchPrefix; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section
set_option linter.unusedSimpArgs false
namespace PA196.Source.FetchPrefix
open M6.Source
structure Store where
  n : Nat
  l : Nat
  x : Nat
  frame : Registers

def registers (s : Store) : Registers := fun r =>
  if r = 0 then s.n else if r = 8 then s.l else if r = 6 then s.x else s.frame r

def configAt (k : Nat) (s : Store) : Configuration := ⟨.at (25+k),registers s⟩
private theorem write_n (s : Store) (v : Nat) :
    write (registers s) 0 v = registers { s with n := v } := by
  funext r
  by_cases h0 : r = 0 <;> by_cases h8 : r = 8 <;> by_cases h6 : r = 6 <;>
    simp_all [write, registers]
private theorem write_l (s : Store) (v : Nat) :
    write (registers s) 8 v = registers { s with l := v } := by
  funext r
  by_cases h0 : r = 0 <;> by_cases h8 : r = 8 <;> by_cases h6 : r = 6 <;>
    simp_all [write, registers]
private theorem write_x (s : Store) (v : Nat) :
    write (registers s) 6 v = registers { s with x := v } := by
  funext r
  by_cases h0 : r = 0 <;> by_cases h8 : r = 8 <;> by_cases h6 : r = 6 <;>
    simp_all [write, registers]
private theorem step_0 (n l x : Nat) (f : Registers) :
    step Program.sites (configAt 0 ⟨n,l,x,f⟩) = if l = 0 then configAt 2 ⟨n,l,x,f⟩ else configAt 1 ⟨n,l-1,x,f⟩ := by
  change step Program.sites ⟨.at 25,registers ⟨n,l,x,f⟩⟩ = _
  have hb : resolveAt Program.sites 25 = some fetchPrefixExpected[0] :=
    fetch_prefix_at ⟨0,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : l = 0
  all_goals simp_all [fetchPrefixExpected, execute, destination, configAt, write_n, write_l, write_x, registers]
private theorem step_1 (n l x : Nat) (f : Registers) :
    step Program.sites (configAt 1 ⟨n,l,x,f⟩) = configAt 9 ⟨n,l,x,f⟩ := by
  change step Program.sites ⟨.at 26,registers ⟨n,l,x,f⟩⟩ = _
  have hb : resolveAt Program.sites 26 = some fetchPrefixExpected[1] :=
    fetch_prefix_at ⟨1,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [fetchPrefixExpected, execute, destination, configAt, write_n, write_l, write_x, registers]
private theorem step_2 (n l x : Nat) (f : Registers) :
    step Program.sites (configAt 2 ⟨n,l,x,f⟩) = if n = 0 then configAt 6 ⟨n,l,x,f⟩ else configAt 3 ⟨n-1,l,x,f⟩ := by
  change step Program.sites ⟨.at 27,registers ⟨n,l,x,f⟩⟩ = _
  have hb : resolveAt Program.sites 27 = some fetchPrefixExpected[2] :=
    fetch_prefix_at ⟨2,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : n = 0
  all_goals simp_all [fetchPrefixExpected, execute, destination, configAt, write_n, write_l, write_x, registers]
private theorem step_3 (n l x : Nat) (f : Registers) :
    step Program.sites (configAt 3 ⟨n,l,x,f⟩) = configAt 4 ⟨n,l+1,x,f⟩ := by
  change step Program.sites ⟨.at 28,registers ⟨n,l,x,f⟩⟩ = _
  have hb : resolveAt Program.sites 28 = some fetchPrefixExpected[3] :=
    fetch_prefix_at ⟨3,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [fetchPrefixExpected, execute, destination, configAt, write_n, write_l, write_x, registers]
private theorem step_4 (n l x : Nat) (f : Registers) :
    step Program.sites (configAt 4 ⟨n,l,x,f⟩) = configAt 5 ⟨n,l,x+1,f⟩ := by
  change step Program.sites ⟨.at 29,registers ⟨n,l,x,f⟩⟩ = _
  have hb : resolveAt Program.sites 29 = some fetchPrefixExpected[4] :=
    fetch_prefix_at ⟨4,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [fetchPrefixExpected, execute, destination, configAt, write_n, write_l, write_x, registers]
private theorem step_5 (n l x : Nat) (f : Registers) :
    step Program.sites (configAt 5 ⟨n,l,x,f⟩) = configAt 2 ⟨n,l,x,f⟩ := by
  change step Program.sites ⟨.at 30,registers ⟨n,l,x,f⟩⟩ = _
  have hb : resolveAt Program.sites 30 = some fetchPrefixExpected[5] :=
    fetch_prefix_at ⟨5,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [fetchPrefixExpected, execute, destination, configAt, write_n, write_l, write_x, registers]
private theorem step_6 (n l x : Nat) (f : Registers) :
    step Program.sites (configAt 6 ⟨n,l,x,f⟩) = configAt 7 ⟨n+1,l,x,f⟩ := by
  change step Program.sites ⟨.at 31,registers ⟨n,l,x,f⟩⟩ = _
  have hb : resolveAt Program.sites 31 = some fetchPrefixExpected[6] :=
    fetch_prefix_at ⟨6,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [fetchPrefixExpected, execute, destination, configAt, write_n, write_l, write_x, registers]
private theorem step_7 (n l x : Nat) (f : Registers) :
    step Program.sites (configAt 7 ⟨n,l,x,f⟩) = if x = 0 then configAt 9 ⟨n,l,x,f⟩ else configAt 8 ⟨n,l,x-1,f⟩ := by
  change step Program.sites ⟨.at 32,registers ⟨n,l,x,f⟩⟩ = _
  have hb : resolveAt Program.sites 32 = some fetchPrefixExpected[7] :=
    fetch_prefix_at ⟨7,by decide⟩
  rw [step_of_resolved hb]
  by_cases hz : x = 0
  all_goals simp_all [fetchPrefixExpected, execute, destination, configAt, write_n, write_l, write_x, registers]
private theorem step_8 (n l x : Nat) (f : Registers) :
    step Program.sites (configAt 8 ⟨n,l,x,f⟩) = configAt 6 ⟨n,l,x,f⟩ := by
  change step Program.sites ⟨.at 33,registers ⟨n,l,x,f⟩⟩ = _
  have hb : resolveAt Program.sites 33 = some fetchPrefixExpected[8] :=
    fetch_prefix_at ⟨8,by decide⟩
  rw [step_of_resolved hb]
  all_goals simp_all [fetchPrefixExpected, execute, destination, configAt, write_n, write_l, write_x, registers]

theorem drain_n (n l x : Nat) (f : Registers) :
    Steps Program.sites (4*n+1) (configAt 2 ⟨n,l,x,f⟩)
      (configAt 6 ⟨0,l+n,x+n,f⟩) := by
  induction n generalizing l x with
  | zero =>
    apply Steps.cons
    rw [step_2]
    simp only [↓reduceIte, Nat.add_zero]
    exact Steps.refl _
  | succ n ih =>
    have he : 4*(n+1)+1 = (4*n+1)+1+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_2]
    simp only [Nat.add_eq_zero_iff, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
    apply Steps.cons
    rw [step_3]
    apply Steps.cons
    rw [step_4]
    apply Steps.cons
    rw [step_5]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (l+1) (x+1)

theorem restore_x (x n l : Nat) (f : Registers) :
    Steps Program.sites (3*x+2) (configAt 6 ⟨n,l,x,f⟩)
      (configAt 9 ⟨n+x+1,l,0,f⟩) := by
  induction x generalizing n with
  | zero =>
    apply Steps.cons
    rw [step_6]
    apply Steps.cons
    rw [step_7]
    simp only [↓reduceIte, Nat.add_zero]
    exact Steps.refl _
  | succ x ih =>
    have he : 3*(x+1)+2 = (3*x+2)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_6]
    apply Steps.cons
    rw [step_7]
    simp only [Nat.add_eq_zero_iff, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
    apply Steps.cons
    rw [step_8]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n+1)

theorem positive (n l : Nat) (f : Registers) :
    Steps Program.sites 2 (configAt 0 ⟨n,l+1,0,f⟩) (configAt 9 ⟨n,l,0,f⟩) := by
  apply Steps.cons
  rw [step_0]
  simp only [Nat.add_eq_zero_iff, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
  apply Steps.cons
  rw [step_1]
  exact Steps.refl _

theorem fresh (n : Nat) (f : Registers) :
    Steps Program.sites (7*n+4) (configAt 0 ⟨n,0,0,f⟩) (configAt 9 ⟨n+1,n,0,f⟩) := by
  have hd := drain_n n 0 0 f
  simp only [Nat.zero_add] at hd
  have h := hd.append (restore_x n 0 n f)
  simp only [Nat.zero_add] at h
  have he : 7*n+4 = ((4*n+1)+(3*n+2))+1 := by omega
  rw [he]
  apply Steps.cons
  rw [step_0]
  simp only [↓reduceIte]
  exact h

#print axioms positive
#print axioms fresh
end PA196.Source.FetchPrefix

