import DiophantineConsistency.ArithmeticRadixAlignment

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticRadixAlignmentChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticRadixAlignment
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (d n : V) : ∃ z : V, Exp.exp (d*n)=1+(Exp.exp d-1)*z :=
  block_quotient d n

example (n : V) : ∃ z : V, Exp.exp (0*n)=1+(Exp.exp (0:V)-1)*z :=
  block_quotient 0 n

example (d u J : V) (hd : 2≤d)
    (he : Exp.exp u=(Exp.exp d-1)*J+1) : u%d=0 :=
  aligned_remainder d u J hd he

example (R : V) : (1:V)=Exp.exp (log (1:V)) :=
  exponential_factor R 1 (one_dvd _)

example (d J R w : V) (hd : 2≤d) (hJ : 0<J)
    (he : Exp.exp R=w*((Exp.exp d-1)*J+1)) :
    0<w ∧ ∃ N : V, 0<N ∧
      (Exp.exp d-1)*J+1=Exp.exp (d*N) ∧
      d*N≤R ∧ w=Exp.exp (R-d*N) :=
  factor_alignment d J R w hd hJ he

-- Zero rank cannot satisfy the positive-coefficient factorization.
example (d J w : V) (hd : 2≤d) (hJ : 0<J) :
    Exp.exp (0:V)≠w*((Exp.exp d-1)*J+1) := by
  intro he
  obtain ⟨_,N,hN,_,hbound,_⟩ := factor_alignment d J 0 w hd hJ he
  have hp : 0<d*N := mul_pos (lt_of_lt_of_le (by simp) hd) hN
  exact (not_lt_of_ge hbound) hp

-- At d=1 the remainder proof's literal 1-residue would instead be zero.
example : (1:ℕ) % (2^1-1)=0 := by decide

#print axioms radix_add_one
#print axioms radix_gt_one
#print axioms block_quotient
#print axioms exp_mod_radix
#print axioms aligned_remainder
#print axioms aligned_exponent
#print axioms exponential_factor
#print axioms factor_alignment
end DiophantineConsistency.ArithmeticRadixAlignmentChecks
