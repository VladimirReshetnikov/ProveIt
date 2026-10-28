import DiophantineConsistency.ArithmeticPellRecurrence

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellRecurrenceChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (time b : V) : ∃! out, runDef.val.Evalb ![out,time,b] := run_total time b

example (time b : V) :
    xDef.val.Evalb ![xcoord time b,time,b] ∧
    yDef.val.Evalb ![ycoord time b,time,b] := by simp

example (b : V) : delta b+1=(b+2)*(b+2) := by unfold delta; ring

example (b : V) : xcoord 1 b=b+2 ∧ ycoord 1 b=1 := by
  simpa only [zero_add,x_zero,y_zero,mul_one,mul_zero,add_zero] using
    And.intro (x_succ (0:V) b) (y_succ (0:V) b)

example (time b : V) :
    xcoord time b*xcoord time b=1+(b+1)*(b+3)*ycoord time b*ycoord time b := norm time b

example (time b : V) : time≤ycoord time b ∧ 1≤xcoord time b :=
  ⟨time_le_y time b,one_le_x time b⟩

example (left right b : V) :
    ycoord (left+right) b=xcoord left b*ycoord right b+ycoord left b*xcoord right b :=
  (addition left right b).2

#print axioms run_defined
#print axioms run_defined_delta
#print axioms x_defined
#print axioms y_defined
#print axioms norm
#print axioms one_le_x
#print axioms y_succ_lt
#print axioms time_le_y
#print axioms addition
end DiophantineConsistency.ArithmeticPellRecurrenceChecks
