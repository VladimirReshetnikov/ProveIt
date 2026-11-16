module
public import M6.Source.Determinism
public import M6.Source.AXGateCompareSteps
@[expose] public section
namespace M6.Source.AXGateCompare
variable {sites : Array Site} {base : Nat} (hbound : Bound sites base)
include hbound

theorem clear_h (t h x : Nat) (f : Registers) :
    Steps sites (2*h+1) (configAt base 5 ⟨t,h,x,f⟩)
      (configAt base 7 ⟨t,0,x,f⟩) := by
  induction h with
  | zero =>
    apply Steps.cons
    rw [step_5 hbound]
    exact Steps.refl _
  | succ h ih =>
    have he : 2*(h+1)+1 = (2*h+1)+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_5 hbound]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_6 hbound]
    exact ih

theorem clear_x (t x : Nat) (f : Registers) :
    Steps sites (3*x+2) (configAt base 7 ⟨t,0,x,f⟩)
      (configAt base 12 ⟨t,0,0,f⟩) := by
  induction x with
  | zero =>
    apply Steps.cons
    rw [step_7 hbound]
    simp only [↓reduceIte]
    apply Steps.cons
    rw [step_9 hbound]
    exact Steps.refl _
  | succ x ih =>
    have he : 3*(x+1)+2 = (3*x+2)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_7 hbound]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_8 hbound]
    apply Steps.cons
    rw [step_5 hbound]
    exact ih

theorem cleanup (t h x : Nat) (f : Registers) :
    Steps sites ((2*h+1)+(3*x+2)) (configAt base 5 ⟨t,h,x,f⟩)
      (configAt base 12 ⟨t,0,0,f⟩) :=
  (clear_h hbound t h x f).append (clear_x hbound t x f)

theorem clear_t (t h x : Nat) (f : Registers) :
    Steps sites (2*t+1) (configAt base 10 ⟨t,h,x,f⟩)
      (configAt base 12 ⟨0,h,x,f⟩) := by
  induction t with
  | zero =>
    apply Steps.cons
    rw [step_10 hbound]
    exact Steps.refl _
  | succ t ih =>
    have he : 2*(t+1)+1 = (2*t+1)+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_10 hbound]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_11 hbound]
    exact ih

/-- Equality destroys T; inequality preserves T. H and X are cleared in both cases. -/
theorem compare (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps sites n (configAt base 0 ⟨t,h,x,f⟩)
      (configAt base 12 ⟨if h=x then 0 else t,0,0,f⟩) := by
  induction h generalizing x with
  | zero =>
    cases x with
    | zero =>
      refine ⟨(2*t+1)+2,by omega,?_⟩
      apply Steps.cons
      rw [step_0 hbound]
      simp only [↓reduceIte]
      apply Steps.cons
      rw [step_4 hbound]
      exact clear_t hbound t 0 0 f
    | succ x =>
      refine ⟨((2*0+1)+(3*x+2))+2,by omega,?_⟩
      apply Steps.cons
      rw [step_0 hbound]
      simp only [↓reduceIte,Nat.zero_ne_add_one]
      apply Steps.cons
      rw [step_4 hbound]
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      exact cleanup hbound t 0 x f
  | succ h ih =>
    cases x with
    | zero =>
      refine ⟨((2*h+1)+(3*0+2))+3,by omega,?_⟩
      apply Steps.cons
      rw [step_0 hbound]
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      apply Steps.cons
      rw [step_1 hbound]
      simp only [↓reduceIte]
      apply Steps.cons
      rw [step_3 hbound]
      exact cleanup hbound t h 0 f
    | succ x =>
      obtain ⟨n,hn,hh⟩ := ih x
      refine ⟨n+3,by omega,?_⟩
      apply Steps.cons
      rw [step_0 hbound]
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel,Nat.add_right_cancel_iff]
      apply Steps.cons
      rw [step_1 hbound]
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      apply Steps.cons
      rw [step_2 hbound]
      exact hh
#print axioms compare
end M6.Source.AXGateCompare

