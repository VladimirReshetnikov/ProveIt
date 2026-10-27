import DiophantineConsistency.ArithmeticPellFirstNorm

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellFirstNormChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellFirstNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (q x k : V) (h : x*x=1+discriminant q*k*k) : ∃ y : V, k=2*y :=
  even_ordinate q x k h
example (Q x k : V) (hQ : 0<Q) (h : x*x=1+Q*(Q+1)*k*k) :
    ∃ time : V, time≤k ∧ xcoord time (2*(Q-1)+1)=x ∧ 2*ycoord time (2*(Q-1)+1)=k :=
  positive_parameter_solution Q x k hQ h
example (q : V) : ∃ time : V, time≤0 ∧ xcoord time (2*q+1)=1 ∧
    2*ycoord time (2*q+1)=0 :=
  solution_index q 1 0 (by simp)
example (q x : V) (h : x*x=1+discriminant q) : False := by
  have hn : x*x=1+discriminant q*1*1 := by simpa using h
  have ht := two_le_ordinate q x 1 (by simp) hn
  exact (not_le_of_gt (by simp : (1:V)<2)) ht
example (q x k : V) (h : x*x=1+discriminant q*k*k) :
    ∃ time r s : V, time≤k ∧ xcoord time (2*q+1)=x ∧ 2*ycoord time (2*q+1)=k ∧
      x=1+2*(q+1)*r ∧ k=2*time+4*(q+1)*s := solution_residues q x k h

#print axioms positive_x
#print axioms x_bound
#print axioms two_le_ordinate
#print axioms norm_advance_iff
#print axioms descent
#print axioms solution_index
#print axioms norm_iff_index
#print axioms even_ordinate
#print axioms positive_solution_index
#print axioms positive_parameter_solution
#print axioms solution_residues
end DiophantineConsistency.ArithmeticPellFirstNormChecks
