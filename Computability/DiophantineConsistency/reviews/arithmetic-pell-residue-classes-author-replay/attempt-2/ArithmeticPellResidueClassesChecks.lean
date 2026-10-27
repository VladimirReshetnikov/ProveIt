import DiophantineConsistency.ArithmeticPellResidueClasses

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellResidueClassesChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellResidueClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (b i j n : V) (hi : 0<i) (hin : i≤n)
    (h : xcoord j b%xcoord n b=xcoord i b%xcoord n b) :
    j%(4*n)=i ∨ (j+i)%(4*n)=0 := x_residue_classes b i j n hi hin h

example (j : V) (h : xcoord j 0%xcoord 1 0=0) :
    j%4=1 ∨ (j+1)%4=0 := by
  simpa only [mul_one] using x_residue_classes 0 1 j 1 (by simp) le_rfl (by simpa using h)

example (b n j : V) (hn : 0<n) (h : xcoord j b%xcoord n b=0) :
    j%(4*n)=n ∨ (j+n)%(4*n)=0 :=
  x_residue_classes b n j n hn le_rfl (by simpa using h)

example (b p t : V) (hp : 0<p)
    (h : (xcoord (2*t) b+xcoord (2*p) b)%xcoord (2*p) b=0) :
    t%(2*p)=p%(2*p) ∨ (t+p)%(2*p)=0 :=
  doubled_step_down b (2*p) p t hp le_rfl (Or.inr h)

example (b j : V) (h : b+2∣xcoord j b) : ∃ k:V,j=2*k+1 := odd_index_witness b j h

/-- The excluded target0 collision is real at the smallest base. -/
example : xcoord (0:V) 0%xcoord 1 0=xcoord 2 0%xcoord 1 0 := by
  have h1 : xcoord (1:V) 0=2 := by simpa using x_succ (0:V) 0
  have hy1 : ycoord (1:V) 0=1 := by simpa using y_succ (0:V) 0
  have h2 : xcoord (2:V) 0=7 := by
    simpa [h1,hy1,delta] using x_succ (1:V) 0
  rw [x_zero,h1,h2]
  have h7 : (7:V)%2=1 := by
    have hh := mod_mul_add_of_lt (3:V) 2 (show (1:V)<2 by simp)
    convert hh using 1 <;> ring
  rw [h7,mod_eq_self_of_lt (show (1:V)<2 by simp)]

#print axioms mod_add_cancel
#print axioms mod_reduce
#print axioms mod_scale
#print axioms x_strictMono
#print axioms x_reflection_add
#print axioms x_reflection
#print axioms x_antiperiod
#print axioms x_antireflection
#print axioms x_four_reflection
#print axioms x_gap
#print axioms x_local_residue
#print axioms x_residue_classes
#print axioms doubled_step_down
#print axioms odd_index_of_base_dvd
#print axioms odd_index_witness
end DiophantineConsistency.ArithmeticPellResidueClassesChecks
