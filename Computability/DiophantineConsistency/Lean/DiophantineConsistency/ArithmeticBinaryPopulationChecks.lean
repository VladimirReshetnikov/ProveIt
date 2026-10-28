import DiophantineConsistency.ArithmeticBinaryPopulation

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticBinaryPopulationChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (n a : V) : ∃! out, prefixDef.val.Evalb ![out,n,a] := prefix_total n a
example (a : V) : ∃! out, populationDef.val.Evalb ![out,a] := population_total a

-- Both block values and the width are arbitrary internal elements.
example (A n b : V) (hb : b<Exp.exp n) :
    population (A*Exp.exp n+b)=population A+population b := concatenate A n b hb

example (n a : V) (ha : a<Exp.exp n) :
    population a+population (Exp.exp n-1-a)=n := complement n a ha

-- Zero width has only the zero low block; no positivity premise is hidden.
example (A : V) : population (A*Exp.exp 0+0)=population A := by simp
example : population (Exp.exp (0:V)-1)=0 := population_exp_sub_one 0

#print axioms prefix_total
#print axioms population_total
#print axioms prefix_le
#print axioms prefix_stable
#print axioms prefix_eq_population
#print axioms prefix_binary
#print axioms population_even
#print axioms population_odd
#print axioms population_le
#print axioms population_div_mod
#print axioms concatenate
#print axioms complement
#print axioms population_exp
#print axioms population_exp_sub_one
end DiophantineConsistency.ArithmeticBinaryPopulationChecks
