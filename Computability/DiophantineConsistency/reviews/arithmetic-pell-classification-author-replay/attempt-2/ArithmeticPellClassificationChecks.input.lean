import DiophantineConsistency.ArithmeticPellClassification

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellClassificationChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellClassification
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (b x y : V) (h : x*x=1+delta b*y*y) :
    ∃ time : V, time≤y ∧ xcoord time b=x ∧ ycoord time b=y := solution_index b x y h

example (b x : V) (h : x*x=1) : x=1 := by
  obtain ⟨time,ht,hx,_⟩ := solution_index b x 0 (by simpa using h)
  have ht0 : time=0 := le_antisymm ht (Arithmetic.zero_le time)
  simpa [ht0] using hx.symm

example (b x y : V) (hy : 0<y) (h : x*x=1+delta b*y*y) :
    ∃ u v : V, 0<u ∧ v<y ∧ u*u=1+delta b*v*v ∧
      x=(b+2)*u+delta b*v ∧ y=u+(b+2)*v := descent b x y hy h

#print axioms positive_x
#print axioms x_bound
#print axioms norm_advance_iff
#print axioms descent
#print axioms solution_index
#print axioms norm_iff_index
end DiophantineConsistency.ArithmeticPellClassificationChecks
