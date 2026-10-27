import DiophantineConsistency.ArithmeticPellPeriodicity

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellPeriodicityChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellPeriodicity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (n b : V) : xcoord (2*n) b+1=2*xcoord n b*xcoord n b := double_x_add_one n b
example (n m b : V) (hm : m≤n) :
    ycoord (n+m) b=ycoord (n-m) b+2*xcoord n b*ycoord m b := reflection n m b hm
example (blocks n start b : V) :
    ∃ r s : V, xcoord (4*n*blocks+start) b=xcoord start b+xcoord n b*r ∧
      ycoord (4*n*blocks+start) b=ycoord start b+xcoord n b*s :=
  period_quotients blocks n start b
example (blocks start b : V) :
    xcoord (4*0*blocks+start) b%xcoord 0 b=xcoord start b%xcoord 0 b ∧
    ycoord (4*0*blocks+start) b%xcoord 0 b=ycoord start b%xcoord 0 b :=
  period_mod blocks 0 start b
example (i n b : V) (hi : i≤n) (h : ycoord i b%xcoord n b=0) : i=0 := by
  apply index_eq_of_mod i 0 n b hi (Arithmetic.zero_le n)
  simpa using h

#print axioms double_x
#print axioms double_x_add_one
#print axioms double_y
#print axioms reflection_add
#print axioms reflection
#print axioms four_quotients
#print axioms period_quotients
#print axioms period_mod
#print axioms y_lt_x
#print axioms index_eq_of_mod
end DiophantineConsistency.ArithmeticPellPeriodicityChecks
