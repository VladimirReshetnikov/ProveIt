module
public import M6.Source.AXPairSteps
public import M6.Source.Cantor
@[expose] public section
namespace M6.Source.AXPair
variable {sites : Array Site} {offset : Nat} (hbound : Bound sites offset)
include hbound
theorem drain_t_xy (t w x y : Nat) (f : Registers) :
    Steps sites (4*t+1) (configAt offset 31 ⟨t,w,x,y,f⟩)
      (configAt offset 35 ⟨0,w,x+t,y+t,f⟩) := by
  induction t generalizing x y with
  | zero =>
    apply Steps.cons
    rw [step_31 hbound]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ t ih =>
    have he : 4*(t+1)+1 = (4*t+1)+1+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_31 hbound]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_32 hbound]
    apply Steps.cons
    rw [step_33 hbound]
    apply Steps.cons
    rw [step_34 hbound]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1) (y+1)

theorem drain_x (t w x y : Nat) (f : Registers) :
    Steps sites (3*x+1) (configAt offset 37 ⟨t,w,x,y,f⟩)
      (configAt offset 40 ⟨t+x,w,0,y,f⟩) := by
  induction x generalizing t with
  | zero =>
    apply Steps.cons
    rw [step_37 hbound]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ x ih =>
    have he : 3*(x+1)+1 = (3*x+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_37 hbound]
    simp only [Nat.add_sub_cancel,Nat.succ_ne_zero,↓reduceIte]
    apply Steps.cons
    rw [step_38 hbound]
    apply Steps.cons
    rw [step_39 hbound]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1)

end M6.Source.AXPair

