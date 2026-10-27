import DiophantineConsistency.ArithmeticPellCongruences

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellCongruencesChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (time b m : V) (hm : m∣b+1) :
    ∃ r s : V, xcoord time b=1+m*r ∧ ycoord time b=time+m*s := residue_quotients time b m hm

example (b m : V) : m∣xcoord 0 b-1 ∧ m∣ycoord 0 b := by simp

example (time b m : V) (hm : m∣b+1) (hp : 0<m) :
    xcoord time b%m=1%m ∧ ycoord time b%m=time%m := residue_mod time b m hm hp

/-- A concrete, unconditional first-index instance in every internal model. -/
example : (4:V)∣2*ycoord 2 1-3-1 := by
  have h := first_difference_four (2:V) 1 1 3 (2*ycoord 2 1) (by norm_num) rfl (by norm_num)
  simpa only [mul_one] using h

example (b x y m : V) (hn : x*x=1+delta b*y*y) (hm : m∣b+1) :
    ∃ time r s : V, time≤y ∧ xcoord time b=x ∧ ycoord time b=y ∧
      x=1+m*r ∧ y=time+m*s := solution_residues b x y m hn hm

example (b left right : V) (h : ycoord left b=ycoord right b) : left=right := index_unique b left right h

#print axioms residue_quotients
#print axioms residue_divisibility
#print axioms residue_mod
#print axioms first_transport
#print axioms first_difference_four
#print axioms solution_residues
#print axioms y_add_ge
#print axioms y_strictMono
#print axioms index_unique
end DiophantineConsistency.ArithmeticPellCongruencesChecks
