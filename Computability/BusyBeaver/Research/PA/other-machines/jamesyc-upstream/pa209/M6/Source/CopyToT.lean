module
public import M6.Source.Determinism
@[expose] public section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace M6.Source.CopyToT

def expected (r : Fin 9) (base : Nat) : Nat → Instruction
  | 0 => .dec r (some (base+4)) (some (base+1))
  | 1 => .inc 1 (some (base+2))
  | 2 => .inc 6 (some (base+3))
  | 3 => .jump (some base)
  | 4 => .dec 6 (some (base+7)) (some (base+5))
  | 5 => .inc r (some (base+6))
  | _ => .jump (some (base+4))

def Bound (sites : Array Site) (r : Fin 9) (base : Nat) :=
  ∀ j : Fin 7, resolveAt sites (base+j.val) = some (expected r base j.val)

def registers (r : Fin 9) (v t x : Nat) (f : Registers) : Registers := fun j =>
  if j = r then v else if j = 1 then t else if j = 6 then x else f j

def config (r : Fin 9) (base pc v t x : Nat) (f : Registers) : Configuration :=
  ⟨.at (base+pc),registers r v t x f⟩

variable {sites : Array Site} {r : Fin 9} {base : Nat}
  (h1 : r ≠ 1) (h6 : r ≠ 6) (hb : Bound sites r base)

private theorem write_r (v t x z : Nat) (f : Registers) :
    write (registers r v t x f) r z = registers r z t x f := by
  funext j
  by_cases hj : j = r <;> simp_all [registers,write]
include h1 in
private theorem write_t (v t x z : Nat) (f : Registers) :
    write (registers r v t x f) 1 z = registers r v z x f := by
  funext j
  by_cases hj : j = r <;> by_cases hj1 : j = 1 <;> simp_all [registers,write]
include h6 in
private theorem write_x (v t x z : Nat) (f : Registers) :
    write (registers r v t x f) 6 z = registers r v t z f := by
  funext j
  by_cases hj : j = r <;> by_cases hj1 : j = 1 <;> by_cases hj6 : j = 6 <;>
    simp_all [registers,write]

include hb h1 h6
private theorem step0 (v t x : Nat) (f : Registers) :
    step sites (config r base 0 v t x f) =
      if v = 0 then config r base 4 v t x f else config r base 1 (v-1) t x f := by
  have h := hb ⟨0,by decide⟩
  change resolveAt sites (base+0) = some (expected r base 0) at h
  rw [config,step_of_resolved h]
  simp [expected,execute,registers,destination,config,write_r]
private theorem step1 (v t x : Nat) (f : Registers) :
    step sites (config r base 1 v t x f) = config r base 2 v (t+1) x f := by
  rw [config,step_of_resolved (hb ⟨1,by decide⟩)]
  simp [expected,execute,destination,config,write_t h1,registers,Ne.symm h1]
private theorem step2 (v t x : Nat) (f : Registers) :
    step sites (config r base 2 v t x f) = config r base 3 v t (x+1) f := by
  rw [config,step_of_resolved (hb ⟨2,by decide⟩)]
  simp [expected,execute,destination,config,write_x h6,registers,Ne.symm h6]
private theorem step3 (v t x : Nat) (f : Registers) :
    step sites (config r base 3 v t x f) = config r base 0 v t x f := by
  rw [config,step_of_resolved (hb ⟨3,by decide⟩)]
  rfl
private theorem step4 (v t x : Nat) (f : Registers) :
    step sites (config r base 4 v t x f) =
      if x = 0 then config r base 7 v t x f else config r base 5 v t (x-1) f := by
  rw [config,step_of_resolved (hb ⟨4,by decide⟩)]
  simp [expected,execute,destination,config,write_x h6,registers,Ne.symm h6]
private theorem step5 (v t x : Nat) (f : Registers) :
    step sites (config r base 5 v t x f) = config r base 6 (v+1) t x f := by
  rw [config,step_of_resolved (hb ⟨5,by decide⟩)]
  simp [expected,execute,destination,config,write_r,registers]
private theorem step6 (v t x : Nat) (f : Registers) :
    step sites (config r base 6 v t x f) = config r base 4 v t x f := by
  rw [config,step_of_resolved (hb ⟨6,by decide⟩)]
  rfl

theorem drain_source (v t x : Nat) (f : Registers) :
    Steps sites (4*v+1) (config r base 0 v t x f)
      (config r base 4 0 (t+v) (x+v) f) := by
  induction v generalizing t x with
  | zero =>
    apply Steps.cons
    rw [step0 h1 h6 hb]
    simp only [Nat.add_zero,↓reduceIte]
    exact Steps.refl _
  | succ v ih =>
    have hh := ih (t+1) (x+1)
    have hn : 4*(v+1)+1 = (4*v+1)+1+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step0 h1 h6 hb]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step1 h1 h6 hb]
    apply Steps.cons
    rw [step2 h1 h6 hb]
    apply Steps.cons
    rw [step3 h1 h6 hb]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem restore_source (v t x : Nat) (f : Registers) :
    Steps sites (3*x+1) (config r base 4 v t x f)
      (config r base 7 (v+x) t 0 f) := by
  induction x generalizing v with
  | zero =>
    apply Steps.cons
    rw [step4 h1 h6 hb]
    simp only [Nat.add_zero,↓reduceIte]
    exact Steps.refl _
  | succ x ih =>
    have hn : 3*(x+1)+1 = (3*x+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step4 h1 h6 hb]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step5 h1 h6 hb]
    apply Steps.cons
    rw [step6 h1 h6 hb]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (v+1)

/-- A proved seven-row source macro: add a preserved parameter into T,
restoring X to zero and preserving every unrelated register. -/
theorem copy (v t : Nat) (f : Registers) :
    Steps sites (7*v+2) (config r base 0 v t 0 f)
      (config r base 7 v (t+v) 0 f) := by
  have a := drain_source h1 h6 hb v t 0 f
  have b := restore_source h1 h6 hb 0 (t+v) v f
  simp only [Nat.zero_add] at a b
  have hn : 7*v+2 = (4*v+1)+(3*v+1) := by omega
  rw [hn]
  exact a.append b

#print axioms copy
end M6.Source.CopyToT

