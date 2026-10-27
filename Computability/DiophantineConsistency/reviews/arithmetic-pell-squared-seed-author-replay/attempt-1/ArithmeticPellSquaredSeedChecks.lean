import DiophantineConsistency.ArithmeticPellSquaredSeed

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellSquaredSeedChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellSquaredSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (R a n : V) : ∃ r s : V,
    xcoord (2*n*R) a=1+ycoord R a*ycoord R a*r ∧
    ycoord (2*n*R) a=2*n*xcoord R a*ycoord R a+ycoord R a*ycoord R a*s :=
  doubled_quotients n R a

example (a : V) : ∃ i : V, ycoord (0*ycoord 0 a) a=i*ycoord 0 a*ycoord 0 a :=
  squared_ordinate 0 a

example (R a : V) (hR : 0<R) :
    ∃ f i : V, 0<f ∧ 0<i ∧
      f=xcoord (R*ycoord R a) a ∧
      ycoord (R*ycoord R a) a=i*ycoord R a*ycoord R a ∧
      f*f=1+delta a*(i*ycoord R a*ycoord R a)*(i*ycoord R a*ycoord R a) :=
  strong_seed R a hR

#print axioms doubled_quotients
#print axioms odd_quotient
#print axioms squared_ordinate
#print axioms strong_seed
end DiophantineConsistency.ArithmeticPellSquaredSeedChecks
