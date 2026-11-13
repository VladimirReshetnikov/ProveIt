module
public import PA196.Source.AXGateSteps
public import M6.Source.AXCode
/-! Arithmetic proof adapted from the corresponding M6 module.
All source-row bindings below refer to the PA196 tree. -/
@[expose] public section
namespace PA196.Source.AXGate
open M6.Source

theorem copy_a (t a d h x y : Nat) (f : Registers) :
    Steps Program.sites (4*a+1) (configAt 3658 ⟨t,a,d,h,x,y,f⟩)
      (configAt 3662 ⟨t,0,d,h,x+a,y+a,f⟩) := by
  induction a generalizing x y with
  | zero =>
    apply Steps.cons
    rw [step_3658]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ a ih =>
    have he : 4*(a+1)+1 = (4*a+1)+1+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_3658]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_3659]
    apply Steps.cons
    rw [step_3660]
    apply Steps.cons
    rw [step_3661]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1) (y+1)

theorem y_to_x (t a d h x y : Nat) (f : Registers) :
    Steps Program.sites (3*y+1) (configAt 3674 ⟨t,a,d,h,x,y,f⟩)
      (configAt 3677 ⟨t,a,d,h,x+y,0,f⟩) := by
  induction y generalizing x with
  | zero =>
    apply Steps.cons
    rw [step_3674]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ y ih =>
    have he : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_3674]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_3675]
    apply Steps.cons
    rw [step_3676]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1)

theorem d_to_h (t a d h x y : Nat) (f : Registers) :
    Steps Program.sites (3*d+1) (configAt 3677 ⟨t,a,d,h,x,y,f⟩)
      (configAt 3680 ⟨t,a,0,h+d,x,y,f⟩) := by
  induction d generalizing h with
  | zero =>
    apply Steps.cons
    rw [step_3677]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ d ih =>
    have he : 3*(d+1)+1 = (3*d+1)+1+1+1 := by omega
    rw [he]
    apply Steps.cons
    rw [step_3677]
    simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step_3678]
    apply Steps.cons
    rw [step_3679]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (h+1)

private theorem compare_registers (t a d h x y t' h' x' : Nat) (f : Registers) :
    M6.Source.AXGateCompare.registers ⟨t',h',x',registers ⟨t,a,d,h,x,y,f⟩⟩ =
      registers ⟨t',a,d,h',x',y,f⟩ := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h3 : r = 3 <;> by_cases h4 : r = 4 <;>
    by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [registers,M6.Source.AXGateCompare.registers]

theorem comparison {base : Nat} (hb : M6.Source.AXGateCompare.Bound Program.sites base)
    (t a d h x y : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps Program.sites n (configAt base ⟨t,a,d,h,x,y,f⟩)
      (configAt (base+12) ⟨if h=x then 0 else t,a,d,0,0,y,f⟩) := by
  obtain ⟨n,hn,hs⟩ := M6.Source.AXGateCompare.compare hb t h x (registers ⟨t,a,d,h,x,y,f⟩)
  refine ⟨n,hn,?_⟩
  simpa only [M6.Source.AXGateCompare.configAt,compare_registers,configAt,Nat.add_zero] using hs

/-- The actual final AX gate clears all five work registers. It preserves the
formula stack W and every unrelated register, and sets T to zero when either
comparison matches the original A; otherwise it preserves T. -/
theorem gate (t a d h : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps Program.sites n (configAt 3658 ⟨t,a,d,h,0,0,f⟩)
      (configAt 3799 ⟨if d=a ∨ h=a then 0 else t,0,0,0,0,0,f⟩) := by
  have first : Steps Program.sites (4*a+1) (configAt 3658 ⟨t,a,d,h,0,0,f⟩)
      (configAt 3662 ⟨t,0,d,h,a,a,f⟩) := by
    simpa only [Nat.zero_add] using copy_a t a d h 0 0 f
  obtain ⟨n,hn,second⟩ := comparison PA196.Source.AXGateCompare.bound3662 t 0 d h a a f
  have third := y_to_x (if h=a then 0 else t) 0 d 0 0 a f
  have fourth := d_to_h (if h=a then 0 else t) 0 d 0 a 0 f
  obtain ⟨m,hm,fifth⟩ := comparison PA196.Source.AXGateCompare.bound3680 (if h=a then 0 else t) 0 0 d a 0 f
  have sixth : Steps Program.sites 1
      (configAt 3692 ⟨if d=a then 0 else if h=a then 0 else t,0,0,0,0,0,f⟩)
      (configAt 3799 ⟨if d=a then 0 else if h=a then 0 else t,0,0,0,0,0,f⟩) := by
    apply Steps.cons
    rw [step_3692]
    exact Steps.refl _
  have third' := third
  have fourth' := fourth
  simp only [Nat.zero_add] at third' fourth'
  have all := ((((first.append second).append third').append fourth').append fifth).append sixth
  refine ⟨(4*a+1)+n+(3*a+1)+(3*d+1)+m+1,by omega,?_⟩
  by_cases hd : d=a <;> by_cases hh : h=a <;> simpa only [hd,hh,↓reduceIte,or_self,or_false,false_or] using all
#print axioms gate
end PA196.Source.AXGate
