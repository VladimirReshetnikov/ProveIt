import Trace74N2FifthGrowth

/-! UNCHECKED DRAFT. Subtraction-free seventh Pell ordinate identity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74N4R7PellIdentity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ordinate_seven (b : V) :
    ycoord 7 b+5*(2*(b+2))^4+1=(2*(b+2))^6+6*(2*(b+2))^2 := by
  have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
  have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
  have hx2 : xcoord 2 b=(b+2)*xcoord 1 b+ArithmeticPellRecurrence.delta b*ycoord 1 b := by
    simpa only [show (1:V)+1=2 by ring] using x_succ (1:V) b
  have hy2 : ycoord 2 b=xcoord 1 b+(b+2)*ycoord 1 b := by
    simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) b
  have hx3 : xcoord 3 b=(b+2)*xcoord 2 b+ArithmeticPellRecurrence.delta b*ycoord 2 b := by
    simpa only [show (2:V)+1=3 by ring] using x_succ (2:V) b
  have hy3 : ycoord 3 b=xcoord 2 b+(b+2)*ycoord 2 b := by
    simpa only [show (2:V)+1=3 by ring] using y_succ (2:V) b
  have hx4 : xcoord 4 b=(b+2)*xcoord 3 b+ArithmeticPellRecurrence.delta b*ycoord 3 b := by
    simpa only [show (3:V)+1=4 by ring] using x_succ (3:V) b
  have hy4 : ycoord 4 b=xcoord 3 b+(b+2)*ycoord 3 b := by
    simpa only [show (3:V)+1=4 by ring] using y_succ (3:V) b
  have hx5 : xcoord 5 b=(b+2)*xcoord 4 b+ArithmeticPellRecurrence.delta b*ycoord 4 b := by
    simpa only [show (4:V)+1=5 by ring] using x_succ (4:V) b
  have hy5 : ycoord 5 b=xcoord 4 b+(b+2)*ycoord 4 b := by
    simpa only [show (4:V)+1=5 by ring] using y_succ (4:V) b
  have hx6 : xcoord 6 b=(b+2)*xcoord 5 b+ArithmeticPellRecurrence.delta b*ycoord 5 b := by
    simpa only [show (5:V)+1=6 by ring] using x_succ (5:V) b
  have hy6 : ycoord 6 b=xcoord 5 b+(b+2)*ycoord 5 b := by
    simpa only [show (5:V)+1=6 by ring] using y_succ (5:V) b
  have hy7 : ycoord 7 b=xcoord 6 b+(b+2)*ycoord 6 b := by
    simpa only [show (6:V)+1=7 by ring] using y_succ (6:V) b
  rw [hy7,hx6,hy6,hx5,hy5,hx4,hy4,hx3,hy3,hx2,hy2,hx1,hy1]
  unfold ArithmeticPellRecurrence.delta
  ring

#print axioms Trace74N4R7PellIdentity.ordinate_seven
end Trace74N4R7PellIdentity
