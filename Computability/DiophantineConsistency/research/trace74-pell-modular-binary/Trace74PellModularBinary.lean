import DiophantineConsistency.ArithmeticPellPeriodicity

/-! Verified modular binary steps for the represented Pell recurrence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74PellModularBinary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellPeriodicity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem same_add {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x+z)%m=(y+w)%m := by
  rw [mod_add hm,mod_add (a:=y) hm,h,h']

private theorem same_mul {m x y z w : V} (hm : 0<m)
    (h : x%m=y%m) (h' : z%m=w%m) : (x*z)%m=(y*w)%m := by
  rw [mod_mul hm,mod_mul (a:=y) hm,h,h']

/-- One binary zero step. The inputs need only be congruent residues;
the outputs are remainders bounded by the same positive modulus. -/
theorem even_step (b t m X Y : V) (hm : 0<m)
    (hx : xcoord t b%m=X%m) (hy : ycoord t b%m=Y%m) :
    xcoord (2*t) b%m=(X*X+delta b*Y*Y)%m ∧
      ycoord (2*t) b%m=(2*X*Y)%m := by
  constructor
  · rw [show 2*t=t+t by ring,(addition t t b).1]
    exact same_add hm (same_mul hm hx hx) (same_mul hm (same_mul hm rfl hy) hy)
  · rw [double_y]
    exact same_mul hm (same_mul hm rfl hx) hy

/-- One binary one step; use the even-step output before the Pell
successor. The formulas involve only the current residues. -/
theorem odd_step (b t m X Y : V) (hm : 0<m)
    (hx : xcoord t b%m=X%m) (hy : ycoord t b%m=Y%m) :
    let A := X*X+delta b*Y*Y
    let B := 2*X*Y
    xcoord (2*t+1) b%m=((b+2)*A+delta b*B)%m ∧
      ycoord (2*t+1) b%m=(A+(b+2)*B)%m := by
  obtain ⟨he,ho⟩ := even_step b t m X Y hm hx hy
  constructor
  · rw [x_succ]
    exact same_add hm (same_mul hm rfl he) (same_mul hm rfl ho)
  · rw [y_succ]
    exact same_add hm he (same_mul hm rfl ho)

#print axioms Trace74PellModularBinary.even_step
#print axioms Trace74PellModularBinary.odd_step
end Trace74PellModularBinary
