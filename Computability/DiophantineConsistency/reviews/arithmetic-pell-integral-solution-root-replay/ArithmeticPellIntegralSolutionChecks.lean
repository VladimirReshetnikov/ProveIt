import DiophantineConsistency.ArithmeticPellIntegralSolution

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellIntegralSolutionChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellIntegralSolution
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (b : V) : ycoord 0 b<xcoord 0 b := y_lt_x b 0

example (b g : V) (hg : 0<g) :
    2*ycoord g b*ycoord g b<ycoord (2*g) b := doubled_y_growth b g hg

/-- M=1 is included; no stronger large-index premise is silently added. -/
example (b n S T A D c : V) (hn : 0<n) (hS : 0<S) (hT : 0<T)
    (hSA : S<A) (hD : D=T*S) (hYM : ycoord 1 b=S*c)
    (hcN : c∣T*ycoord n b) (hbig : A*D*D<c) : (1:V)∣n :=
  large_index_multiple b n 1 S T A D c hn (by simp) hS hT hSA hD hYM hcN hbig

example (a c p i f : V) (hp : 0<p) (hi : 0<i) (hf : 0<f)
    (hcp : c=ycoord p a)
    (hn : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))
    (hb : (a+2)*delta a*delta a<c) :
    ∃ m : V, 0<m ∧ p∣m ∧ f=xcoord m a ∧ i*c*c=delta a*ycoord m a :=
  integral_solution a c p i f hp hi hf hcp hn hb

example (a c p i f : V) (hp : 0<p) (hi : 0<i) (hf : 0<f)
    (hcp : c=ycoord p a)
    (hn : (i*c*c)*(i*c*c)=delta a*(f*f-1))
    (hb : (a+2)*delta a*delta a<c) :
    ∃ m : V, 0<m ∧ p∣m ∧ f=xcoord m a ∧ i*c*c=delta a*ycoord m a :=
  integral_solution_tsub a c p i f hp hi hf hcp hn hb

#print axioms y_lt_x
#print axioms doubled_y_growth
#print axioms large_index_multiple
#print axioms integral_solution
#print axioms integral_solution_tsub
end DiophantineConsistency.ArithmeticPellIntegralSolutionChecks
